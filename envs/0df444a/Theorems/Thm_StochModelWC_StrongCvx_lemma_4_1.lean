-- Prove2me | Theorems.Thm_StochModelWC_StrongCvx_lemma_4_1
-- name    : StochModelWC.StrongCvx.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:42:11.655882+00:00
-- url     : https://prove2.me/theorems/0ffd71d5-a1d6-4778-97a7-c9297e6215a4
-- title:
--   Lemma 4.1 — φ is (τ+η)-weakly convex and f is 𝖫-Lipschitz on U
-- statement:
--   Let $\varphi=f+r$ with $r:\mathbb R^d\to\mathbb R\cup\{\infty\}$ proper (nonempty domain $D$) and $f:\mathbb R^d\to\mathbb R$ locally Lipschitz, and suppose Assumption B holds with constants $\tau,\eta,\mathsf L$, the open convex set $U\supseteq D$, the model $f_x(y,\xi)$ and the function $L(\xi)$. Then $\varphi$ is $(\tau+\eta)$-weakly convex, and
--   $$|f(x)-f(y)|\le\mathsf L\|x-y\|\qquad\text{for all }x,y\in U. \tag{4.3}$$
--
--   In the strongly convex setting $\tau=0$, $\eta=-\mu$ the lemma says that $\varphi$ is $\mu$-strongly convex, in particular convex, which is what allows the function gap at a weighted average of iterates to be bounded by the weighted average of the gaps (Theorem 4.2); the Lipschitz bound enters the one-step estimate (4.8).
--
--   **Formalization Note** $r$ is encoded by its domain $D$ and its real values on $D$; weak convexity of $\varphi$ is convexity of $x\mapsto\varphi(x)+\frac{\tau+\eta}{2}\|x\|^2$ on $D$.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 18, Lemma 4.1, (4.3)

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic
import Definitions.Def_StochModelWC_ModelBased_AssumptionB

open MeasureTheory Filter Topology

namespace StochModelWC.StrongCvx

/-- Lemma 4.1 (p. 18): under Assumption B, `φ = f + r` is `(τ + η)`-weakly convex (on `dom r = D`) and `f` is
`L`-Lipschitz on `U`. -/
theorem lemma_4_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (τ η L : ℝ) (Lfun : Ω → ℝ)
    (hD : D.Nonempty) (hf : LocallyLipschitz f)
    (hB : StochModelWC.ModelBased.AssumptionB P U D f r model τ η L Lfun) :
    StochModelWC.ModelBased.IsWeaklyConvexOn D (τ + η) (fun y => f y + r y) ∧
      ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ L * ‖x - y‖ := by sorry

end StochModelWC.StrongCvx
