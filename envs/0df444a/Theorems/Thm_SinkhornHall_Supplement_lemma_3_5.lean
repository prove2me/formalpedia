-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_lemma_3_5
-- name    : SinkhornHall.Supplement.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:10:01.31401+00:00
-- url     : https://prove2.me/theorems/0d3df1cf-7cde-474e-96ef-83eca4116cb8
-- title:
--   Lemma 3.5 — the refined diagonal blocks $A[I_{\kappa,\alpha},J_{\kappa,\alpha}]$ are $(r^{\kappa,\alpha}/R_\kappa,c^{\kappa,\alpha}/C_\kappa)$-scalable
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). A set $X\sqcup Y$ of rows $X$ and columns $Y$ is **stable** if $A_{ij}=0$ for all $i\in X$, $j\in Y$. $\operatorname{Conv}\mathcal S$ is the convex hull in $\mathbb R^2$ of the points $(r(X),c(Y))$ of the stable sets, and $X\sqcup Y$ is **extreme** if $(r(X),c(Y))$ is a nonzero extreme point of $\operatorname{Conv}\mathcal S$. The extreme stable sets ordered as $[n]=X_0\supset X_1\supset\dots\supset X_\theta=\emptyset$, $\emptyset=Y_0\subset\dots\subset Y_\theta=[m]$ give the partitions $I_\kappa=X_{\kappa-1}\setminus X_\kappa$, $J_\kappa=Y_\kappa\setminus Y_{\kappa-1}$ ($\kappa=1,\dots,\theta$), with $R_\kappa=r(I_\kappa)$, $C_\kappa=c(J_\kappa)$, and $\rho^*_i=(C_\kappa/R_\kappa)\,r_i$ for $i\in I_\kappa$. Let $0<\lambda_1<\dots<\lambda_\theta<1$ be the critical parameters of $\max\{(1-\lambda)r(X)+\lambda c(Y): X\sqcup Y \text{ stable}\}$ (3.9) (those at which the maximizer is not unique), $\mathcal S_\kappa$ the family of maximizers at $\lambda_\kappa$, and in each $\mathcal S_\kappa$ a maximal chain $X_{\kappa-1}=X_{\kappa,0}\supset\dots\supset X_{\kappa,\alpha_\kappa}=X_\kappa$, $Y_{\kappa-1}=Y_{\kappa,0}\subset\dots\subset Y_{\kappa,\alpha_\kappa}=Y_\kappa$, with $I_{\kappa,\alpha}=X_{\kappa,\alpha-1}\setminus X_{\kappa,\alpha}$, $J_{\kappa,\alpha}=Y_{\kappa,\alpha}\setminus Y_{\kappa,\alpha-1}$ (3.10).
--
--   For every such choice, each submatrix $A[I_{\kappa,\alpha},J_{\kappa,\alpha}]$ is (exactly) $(r^{\kappa,\alpha}/R_\kappa,\ c^{\kappa,\alpha}/C_\kappa)$-scalable, where $r^{\kappa,\alpha}$, $c^{\kappa,\alpha}$ are the restrictions of $r$, $c$.
--
--   The scalings of these blocks are the pieces of the Sinkhorn limit (Theorem 3.6).
--
--   Differences from the source:
--   - encoding: "the" ordered family of extreme stable sets → every `ExtremeChain` (an enumeration of exactly the extreme stable sets with $X$ strictly decreasing and $Y$ strictly increasing); reason: Lemma 3.1 makes the enumeration unique, so quantifying over every one is the paper's claim
--   - reading: critical parameter, "a minimizer is not unique" (p.13) → the maximizer of (3.9) is not unique; reason: (3.9) is a maximization, the minimizer refers to the equivalent minimum-cut problem
--   - encoding: "choose a maximal chain" in each $\mathcal S_\kappa$ → every `RefinedChain` (increasing enumeration of all critical parameters, a chain in each $\mathcal S_\kappa$ from $X_{\kappa-1}\sqcup Y_{\kappa-1}$ to $X_\kappa\sqcup Y_\kappa$ to which no member of $\mathcal S_\kappa$ can be added); reason: the paper allows any choice
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 3.5, p.14

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL
import Definitions.Def_SinkhornHall_Supplement_Extreme

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Lemma 3.5 (the refined blocks are scalable).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 3.5, p.14: "Each submatrix A[I_{κ,α}, J_{κ,α}] is
(r^{κ,α}/R_κ, c^{κ,α}/C_κ)-scalable."

Setting of §2 and §3 (pp.4–5, p.8, p.10): `A` is a nonnegative `n × m` matrix with neither zero
rows nor zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not
assumed. `S` is the family of stable sets of `G(A)`.
For each `κ`, `{X_{κ,α} ⊔ Y_{κ,α}}_α` is a maximal chain from `X_{κ−1} ⊔ Y_{κ−1}` to `X_κ ⊔ Y_κ`
in the family `S_κ` of maximizers of (3.9) at the critical parameter `λ_κ` (pp.13–14);
`I_{κ,α}`, `J_{κ,α}` are (3.10), `r^{κ,α}`, `c^{κ,α}` the restrictions of `r`, `c`.

**Formalization Note.** Stated for every ordered family of extreme stable sets (`ExtremeChain`) and
every choice of the critical parameters and maximal chains (`RefinedChain`), as the paper says
"Choose a maximal set (chain)". Scalability is exact: a scaling with positive vectors and the exact
marginals (`Scalable`). -/
theorem lemma_3_5 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j)
    (ch : ExtremeChain A r c) (rc : RefinedChain ch) :
    ∀ (k : Fin ch.θ) (a : Fin (rc.α k)),
      Scalable (fun (i : {i // i ∈ rc.I k a}) (j : {j // j ∈ rc.J k a}) => A i j)
        (fun i => r i / ch.Rk k) (fun j => c j / ch.Ck k) := by sorry

end SinkhornHall.Supplement
