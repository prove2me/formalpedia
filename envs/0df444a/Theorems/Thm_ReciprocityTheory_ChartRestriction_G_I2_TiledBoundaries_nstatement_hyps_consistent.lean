-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_nstatement_hyps_consistent
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.nstatement_hyps_consistent
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:13:35.150903+00:00
-- url     : https://prove2.me/theorems/ced73f5a-45cc-5c7f-bab9-873c3e8d1179
-- title:
--   Tiled Boundaries: nstatement hyps consistent
-- statement:
--   The Tiled Boundaries construction uses the nstatement hyps consistent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/NstatementHypsConsistent.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/NstatementHypsConsistent.lean#L71-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 NumberField Complex
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.nstatement_hyps_consistent (q n : ℕ) (hq : 1 ≤ q) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (X : PT E)
      (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim) (s : (Fin 1 → Vsp X.dim) → ℂ)
      (K : Finset (Fin n → Vsp X.dim)),
      1 ≤ q ∧ IsPi X q π ∧ s ∈ X.Sec 1 1 ∧ s ≠ 0 ∧ IsReps X q n π K := by sorry
