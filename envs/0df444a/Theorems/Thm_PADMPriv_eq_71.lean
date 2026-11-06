-- Prove2me | Theorems.Thm_PADMPriv_eq_71
-- name    : PADMPriv.eq_71
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:20.800422+00:00
-- url     : https://prove2.me/theorems/0e9add78-5c95-48f3-b7d4-e4f14f7f6ca4
-- title:
--   Eq. (71) — the fixed points $\bar u_\star$ of $\bar T$ and $u_\star$ of $T_F$ satisfy $\|\bar u_\star-u_\star\|_2^2\le L^2(\beta+\varrho_g)/(\varrho_g\beta^2\omega_A)$
-- statement:
--   Assume: $A$, $B$ have full row rank and $m\ge1$; $(R,P_R)$ is a probability space and $f:\mathbb R^p\times R\to\mathbb R$ is such that each $f(\cdot,d)$ is convex, differentiable and $L$-Lipschitz (Proposition 4.1), each $f(x,\cdot)$ is measurable and integrable, and $F(x)=\mathbb E_d f(x,d)$; the samplewise recovery condition $f(VAx,d)\le f(x,d)$ for all $x$ and $P_R$-a.e. $d$ (25) holds; $g$ is convex and $B$-induced $\varrho_g$-strongly convex.
--   Let $\beta>0$. If $\bar u_\star$ is a fixed point of the mean sample operator $\bar T(u)=\mathbb E_{d\sim P_R}[T_{f(\cdot,d)}(u)]$ and $u_\star$ a fixed point of the population operator $T_F$, then
--   $$
--   \|\bar u_\star-u_\star\|_2^2\le\frac{L^2(\beta+\varrho_g)}{\varrho_g\beta^2\omega_A}. \tag{71}
--   $$
--
--   This controls the bias between the operator the private iteration actually averages and the population operator.
--
--   **Formalization Note** The proximal problems (13) for every $f(\cdot,d)$ and for $g$ are assumed to have minimizers.
--
--   Differences from the source:
--   - generalization: β = ϱ_g n/(8 ln(en)) (the setting of Theorem 5.2) → any β > 0; reason: (71) and its derivation on pp.31–33 use only β > 0; the source's β is a special case
--   - encoding: ū⋆, u⋆ the fixed points of T̄ and T_F → any fixed points ū⋆, u⋆; reason: both operators are contractions (Proposition 5.1 and p.30), so the fixed points are unique
--   - encoding: F(x) := E_{d∼P_R}[f(x, d)] → f(x, ·) measurable and P_R-integrable for every x; reason: needed for the expectation to be defined; excludes only undefined cases
--   - encoding: ω_A > 0 the smallest eigenvalue of AAᵀ → hypothesis 0 < m; reason: ω_A is undefined for m = 0
--   - encoding: the sample proximal operators P_{β,f(·,d),A} used as everywhere defined → hypothesis that (13) for f(·,d) has a minimizer for every record d and input u; reason: Algorithm 1 is undefined otherwise; excludes only undefined cases
--   - encoding: P_{β,g,B} used as everywhere defined → hypothesis that (13) for g has a minimizer at every input; reason: T_{f_k} is undefined otherwise; excludes only undefined cases
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), A.14, Eq. (71), p.33 (proof of Theorem 5.2)

import Mathlib
import Definitions.Def_PADMPriv_padmOp
import Definitions.Def_PADMPriv_meanSampleOp
import Definitions.Def_PADMPriv_popLoss
import Definitions.Def_PADMPriv_pinvRight
import Definitions.Def_PADMPriv_omegaA
import Definitions.Def_PADMPriv_IsInducedStronglyConvex

namespace PADMPriv

open MeasureTheory

/-- A.14, Eq. (71) of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.33 (proof of Theorem 5.2): under the hypotheses of
Proposition 4.1, the samplewise recovery condition (25) and `B`-induced `ϱ_g`-strong convexity of
`g`, the fixed point `ū⋆` of the mean sample operator `T̄(u) = E_d T_{f(·,d)}(u)` and the fixed point
`u⋆` of `T_F`, `F(x) = E_d f(x, d)`, satisfy `‖ū⋆ − u⋆‖₂² ≤ L²(β + ϱ_g)/(ϱ_g β² ω_A)`.

**Formalization Note** `β > 0` is arbitrary here (the bound does not use the parameter choice of
Theorem 5.2). `f(x, ·)` is measurable and `P_R`-integrable for each `x` (so that `F` is defined);
`m ≥ 1`; `A`, `B` full row rank (standing assumption, p.6); `f(·, d)`, `g` real-valued convex; the
proximal problems (13) for every `f(·, d)` and for `g` are assumed to have minimizers. (25) is
`∀ x, P_R-a.e. d, f(VAx, d) ≤ f(x, d)`. -/
theorem eq_71 {m p l : ℕ} {R : Type*} [MeasurableSpace R]
    (hm : 0 < m) (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin l) ℝ)
    (c : EuclideanSpace ℝ (Fin m)) (hA : A.rank = m) (hB : B.rank = m)
    (PR : Measure R) [IsProbabilityMeasure PR]
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (L : NNReal)
    (hfconv : ∀ d, ConvexOn ℝ Set.univ (fun x => f x d))
    (hfdiff : ∀ d, Differentiable ℝ (fun x => f x d))
    (hfLip : ∀ d, LipschitzWith L (fun x => f x d))
    (hfmeas : ∀ x, Measurable (fun d => f x d)) (hfint : ∀ x, Integrable (fun d => f x d) PR)
    (hrec : ∀ x, ∀ᵐ d ∂PR,
      f (Matrix.toEuclideanLin (pinvRight A) (Matrix.toEuclideanLin A x)) d ≤ f x d)
    (g : EuclideanSpace ℝ (Fin l) → ℝ) (hg : ConvexOn ℝ Set.univ g) (ϱg : ℝ)
    (hgsc : IsInducedStronglyConvex B ϱg g)
    (β : ℝ) (hβ : 0 < β) (hfprox : ∀ d u, ∃ x, IsProxMin β (fun x => f x d) A u x)
    (hgprox : ∀ v, ∃ y, IsProxMin β g B v y)
    (ubar ustar : EuclideanSpace ℝ (Fin m))
    (hubar : meanSampleOp β f PR g A B c ubar = ubar)
    (hustar : padmOp β (popLoss f PR) g A B c ustar = ustar) :
    ‖ubar - ustar‖ ^ 2 ≤ (L : ℝ) ^ 2 * (β + ϱg) / (ϱg * β ^ 2 * omegaA A) := by sorry

end PADMPriv
