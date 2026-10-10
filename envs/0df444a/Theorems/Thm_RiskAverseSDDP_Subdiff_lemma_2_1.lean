-- Prove2me | Theorems.Thm_RiskAverseSDDP_Subdiff_lemma_2_1
-- name    : RiskAverseSDDP.Subdiff.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T04:31:57.551981+00:00
-- url     : https://prove2.me/theorems/772e04b9-ba42-4370-95d3-d439b90a9cc1
-- title:
--   Lemma 2.1 (repaired: strict Slater point for g, Slater point in ri dom f) — subdifferential of the value function (2.4)
-- statement:
--   Consider the value function
--   $$\mathcal Q(x)=\inf\{f(x,y):\ y\in Y,\ Ax+By=b,\ g(x,y)\le 0\},\qquad x\in\mathbb R^m,$$
--   of (2.1), where $X\subseteq\mathbb R^m$ and $Y\subseteq\mathbb R^n$ are nonempty, compact and convex, $A\in\mathbb R^{q\times m}$, $B\in\mathbb R^{q\times n}$, $b\in\mathbb R^q$. Assume (H): $f:\mathbb R^m\times\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is lower semicontinuous, proper and convex; each $g_i$ is convex and lower semicontinuous; and $X^\varepsilon\times Y\subseteq\operatorname{dom}(f)$ for some $\varepsilon>0$. Assume moreover
--
--   1. (R1) every $g_i$ is real-valued;
--   2. (R2)–(R3) there is $(\bar x,\bar y)\in X\times\operatorname{ri}(Y)$ with $A\bar x+B\bar y=b$, $g_i(\bar x,\bar y)<0$ for every $i$, and $(\bar x,\bar y)\in\operatorname{ri}(\operatorname{dom}f)$.
--
--   Let $x_0\in X$ with $S(x_0)\ne\emptyset$. Then $\operatorname{Sol}(x_0)\ne\emptyset$, and for every $y_0\in\operatorname{Sol}(x_0)$, with $I(x_0,y_0)=\{i: g_i(x_0,y_0)=0\}$: $s\in\partial\mathcal Q(x_0)$ if and only if
--   $$(s,0)\in\partial f(x_0,y_0)+\big\{[A^\top;B^\top]\lambda:\lambda\in\mathbb R^q\big\}+\Big\{\sum_{i\in I(x_0,y_0)}\mu_i\,\partial g_i(x_0,y_0):\mu_i\ge 0\Big\}+\big\{\{0\}\times\mathcal N_Y(y_0)\big\}.\tag{2.4}$$
--
--   Formula (2.4) computes subgradients of the value function of a convex program whose parameter enters the objective and the nonlinear constraints, without introducing copies of $x$ as new variables. In the paper it gives the slopes of the cuts of the risk-averse SDDP method.
--
--   **Formalization Note (repair).** As printed — extended-valued lower semicontinuous $g_i$ and the Slater-type condition $(\bar x,\bar y)\in X\times\operatorname{ri}(Y)$, $(\bar x,\bar y)\in C_1\cap\operatorname{ri}(C_2)$ — the lemma is false: with $m=n=1$, $X=Y=[-1,1]$, $A=B=0$, $b=0$, $g(x,y)=y^2$, $f(x,y)=y$ the hypotheses hold, $\mathcal Q\equiv0$ so $0\in\partial\mathcal Q(0)$, but no $s$ satisfies (2.4); and with $Y=\{0\}$, $g\equiv-1$, $f(x,y)=-\sqrt y$ ($+\infty$ for $y<0$), $\partial\mathcal Q(0)=\{0\}$ while $\partial f(0,0)=\emptyset$. The repair adds (R1)–(R3) and keeps everything else; under it every step of the printed proof is valid. In Lean, (2.4) is written with explicit witnesses $u\in\partial f(x_0,y_0)$, $\lambda$, $\mu_i\ge0$ and $w_i\in\partial g_i(x_0,y_0)$ for $i\in I$, and $\nu\in\mathcal N_Y(y_0)$, with $s=u_x+A^\top\lambda+\sum_I\mu_i(w_i)_x$ and $0=u_y+B^\top\lambda+\sum_I\mu_i(w_i)_y+\nu$. $\partial\mathcal Q(x_0)$ is the subdifferential on all of $\mathbb R^m$ of the extended-real function $\mathcal Q$, not relative to $X$.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, pp. 3–4, Lemma 2.1, formula (2.4) (repaired hypotheses)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Subdiff_Model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace

namespace RiskAverseSDDP.Subdiff

open ConvexProgram

/-- Lemma 2.1, formula (2.4), pp. 3–4, repaired: (R1) every `g_i` is real-valued, (R2) the
Slater point is strict for `g` and (R3) lies in `ri(dom f)`. Under (H), with `X`, `Y` nonempty,
compact and convex, `x₀ ∈ X` and `S(x₀) ≠ ∅`: `Sol(x₀) ≠ ∅`, and for every `y₀ ∈ Sol(x₀)`,
`s ∈ ∂𝒬(x₀)` iff
`(s, 0) ∈ ∂f(x₀, y₀) + {[Aᵀ; Bᵀ]λ} + {Σ_{i ∈ I(x₀,y₀)} μ_i ∂g_i(x₀, y₀) : μ_i ≥ 0} + {0} × 𝒩_Y(y₀)`. -/
theorem lemma_2_1 {m n q p : ℕ} (P : ConvexProgram m n q p) (X : Set (E m))
    (hX : X.Nonempty ∧ IsCompact X ∧ Convex ℝ X)
    (hY : P.Y.Nonempty ∧ IsCompact P.Y ∧ Convex ℝ P.Y)
    (hH : P.AssumptionH X)
    (hR1 : ∀ i z, P.g i z ≠ ⊤)
    (hSlater : P.RepairedSlater X)
    (x₀ : E m) (hx₀ : x₀ ∈ X) (hS : (P.S x₀).Nonempty) :
    (P.Sol x₀).Nonempty ∧ ∀ y₀ ∈ P.Sol x₀, ∀ s : E m,
      s ∈ subdiff P.Q x₀ ↔
        ∃ u ∈ subdiffProd P.f (x₀, y₀), ∃ lam : E q, ∃ μ : Fin p → ℝ,
          ∃ w : Fin p → E m × E n, ∃ ν ∈ FirstOrderOpt.ConvexTheory.normalCone P.Y y₀,
            (∀ i ∈ P.active x₀ y₀, 0 ≤ μ i ∧ w i ∈ subdiffProd (P.g i) (x₀, y₀)) ∧
            s = u.1 + Matrix.toEuclideanLin P.A.transpose lam + ∑ i ∈ P.active x₀ y₀, μ i • (w i).1 ∧
            (0 : E n) = u.2 + Matrix.toEuclideanLin P.B.transpose lam +
              ∑ i ∈ P.active x₀ y₀, μ i • (w i).2 + ν := by sorry

end RiskAverseSDDP.Subdiff
