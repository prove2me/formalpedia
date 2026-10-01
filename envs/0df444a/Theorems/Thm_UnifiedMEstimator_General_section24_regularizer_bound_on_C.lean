-- Prove2me | Theorems.Thm_UnifiedMEstimator_General_section24_regularizer_bound_on_C
-- name    : UnifiedMEstimator.General.section24_regularizer_bound_on_C
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:13:18.544983+00:00
-- url     : https://prove2.me/theorems/c1309bc5-a27b-460a-a2f9-52e6517251df
-- title:
--   On $\mathbb C$, $\mathcal R(\Delta)\le4\Psi(\overline{\mathcal M})\|\Delta\|$ when $\theta^*\in\mathcal M$ (Section 2.4, p. 10)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $\mathcal R$ a norm on $E$, and $\mathcal M\subseteq\overline{\mathcal M}$ subspaces of $E$. Write $\Delta_S$ for the orthogonal projection of $\Delta$ onto a subspace $S$, $\Psi$ for the subspace compatibility constant and $\mathbb C(\mathcal M,\overline{\mathcal M}^\perp;\theta^*)$ for the set of Eq. (17).
--
--   Suppose that $\theta^*\in\mathcal M$ and $\Delta\in\mathbb C(\mathcal M,\overline{\mathcal M}^\perp;\theta^*)$. Then $\mathcal R(\Delta_{\overline{\mathcal M}^\perp})\le3\,\mathcal R(\Delta_{\overline{\mathcal M}})$, and
--
--   $$
--   \mathcal R(\Delta)\le\mathcal R(\Delta_{\overline{\mathcal M}^\perp})+\mathcal R(\Delta_{\overline{\mathcal M}})\le4\,\mathcal R(\Delta_{\overline{\mathcal M}})\le4\,\Psi(\overline{\mathcal M})\,\|\Delta\| .
--   $$
--
--   This is the step at which the compatibility constant $\Psi(\overline{\mathcal M})$ enters the analysis: on the set $\mathbb C$ the regularizer is controlled by the error norm. It is used to derive restricted strong convexity from bounds of the form (20), and the same comparison appears in the error bound of Theorem 1.
--
--   **Formalization Note** The paper's display is a chain; each link is a separate conjunct. The standing assumption $\mathcal M\subseteq\overline{\mathcal M}$ of Section 2.2 is a hypothesis; decomposability is not needed for this step and is not assumed.
-- source:
--   Negahban, Ravikumar, Wainwright and Yu, A Unified Framework for High-Dimensional Analysis of M-Estimators with Decomposable Regularizers, arXiv:1010.2731v3, p. 10, Section 2.4, first display

import Mathlib
import Definitions.Def_UnifiedMEstimator_General_Core

namespace UnifiedMEstimator.General

/-- Section 2.4, p. 10, first display: if `θ* ∈ M` (with `M ⊆ M̄`), then every `Δ` in
`C(M, M̄⊥; θ*)` satisfies `R(Δ_{M̄⊥}) ≤ 3R(Δ_{M̄})` and
`R(Δ) ≤ R(Δ_{M̄⊥}) + R(Δ_{M̄}) ≤ 4R(Δ_{M̄}) ≤ 4Ψ(M̄)‖Δ‖`. -/
theorem section24_regularizer_bound_on_C
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (R : E → ℝ) (M Mbar : Submodule ℝ E) (θstar Δ : E)
    (hR : IsNormFn R) (hle : M ≤ Mbar) (hθ : θstar ∈ M)
    (hΔ : Δ ∈ setC R M Mbar θstar) :
    R (Mbarᗮ.starProjection Δ) ≤ 3 * R (Mbar.starProjection Δ) ∧
    R Δ ≤ R (Mbarᗮ.starProjection Δ) + R (Mbar.starProjection Δ) ∧
    R (Mbarᗮ.starProjection Δ) + R (Mbar.starProjection Δ) ≤ 4 * R (Mbar.starProjection Δ) ∧
    4 * R (Mbar.starProjection Δ) ≤ 4 * compat R Mbar * ‖Δ‖ := by sorry

end UnifiedMEstimator.General
