-- Prove2me | Theorems.Thm_ProbMetricStab_TwoStage_pfu_contains_P2
-- name    : ProbMetricStab.TwoStage.pfu_contains_P2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:50.807979+00:00
-- url     : https://prove2.me/theorems/e5758a36-28c3-4a45-bafb-3fa9f3c9477e
-- title:
--   p. 13, after Proposition 3.2 — 𝒫_{ℱ_𝒰} ⊇ 𝒫₂(Ξ) for every nonempty bounded 𝒰
-- statement:
--   Consider the linear two-stage program (8) with polyhedra $X\ne\emptyset$ and $\Xi$, affine data, and assume (A1). Let $\mathcal U\subseteq\mathbb R^m$ be nonempty and bounded.
--
--   Then every probability measure on $\Xi$ with finite second moment belongs to $\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$:
--
--   $$\mathcal P_{\mathcal F_{\mathcal U}}\supseteq\Big\{\nu\in\mathcal P(\Xi):\int_\Xi\|\xi\|^2\,\nu(d\xi)<\infty\Big\}=\mathcal P_2(\Xi),$$
--
--   that is, for every $\nu\in\mathcal P_2(\Xi)$, $\int_\Xi\inf_{x\in X,\|x\|\le r}f_0(\xi,x)\,\nu(d\xi)>-\infty$ for each $r>0$ and $\sup_{x\in X\cap\operatorname{cl}\mathcal U}\int_\Xi f_0(\xi,x)\,\nu(d\xi)<\infty$.
--
--   This is what allows the general stability theory of Section 2, which works on $\mathcal P_{\mathcal F_{\mathcal U}}$, to be applied to all perturbations with finite second moments.
--
--   **Formalization Note** The page derives the inclusion from two explicit integral bounds with the constant $K$ of Proposition 3.2; the statement records the conclusion, membership in $\mathcal P_{\mathcal F_{\mathcal U}}$ as defined on p. 4 (with $d=0$), so no constant appears.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 13, display after Proposition 3.2

import Mathlib
import Definitions.Def_ProbMetricStab_TwoStage_Model

namespace ProbMetricStab.TwoStage

/-- Display after Proposition 3.2 (p. 13): under (A1), for every nonempty bounded `𝒰 ⊆ ℝ^m`,
`𝒫_{ℱ_𝒰} ⊇ {ν ∈ 𝒫(Ξ) : ∫_Ξ ‖ξ‖² ν(dξ) < ∞} = 𝒫₂(Ξ)` for the integrand `f₀` of (8). -/
theorem pfu_contains_P2 {m s r mbar : ℕ} (P : Data m s r mbar) (hP : P.Standing) (hA1 : P.A1)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hU : U.Nonempty) (hUb : Bornology.IsBounded U) :
    Pp P.Ξ 2 ⊆ PFU P.X P.Ξ P.f0 U := by sorry

end ProbMetricStab.TwoStage
