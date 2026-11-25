-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_sign_of_bdd
-- name    : ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:27.178789+00:00
-- url     : https://prove2.me/theorems/c58ce7ac-537f-5ac6-bcc8-e5362f971cad
-- title:
--   Bounded Section Algebra: sign of bdd
-- statement:
--   The Bounded Section Algebra construction uses the sign of bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoundedSectionAlgebra.lean#L275-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoundedSectionAlgebra.lean#L275-L279

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd (h3d : ModerateCoefficientPositivity (E := E)) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (h : X.fj la ξ ν P x ≠ 0) : ∀ τ, 0 ≤ ν τ := by sorry
