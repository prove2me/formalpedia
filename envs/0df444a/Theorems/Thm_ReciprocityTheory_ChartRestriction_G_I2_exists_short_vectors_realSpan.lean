-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_exists_short_vectors_realSpan
-- name    : ReciprocityTheory.ChartRestriction.G.I2.exists_short_vectors_realSpan
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:30:29.94253+00:00
-- url     : https://prove2.me/theorems/bc1c1a3e-9c54-47c9-b389-26399637ad4e
-- title:
--   I2: exists short vectors real Span
-- statement:
--   The I2 construction uses the exists short vectors real Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitU.lean#L99-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitU.lean#L99-L266

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.exists_short_vectors_realSpan (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hsat : ∀ x ∈ X.L, x ∈ IR I → x ∈ I) (hla : 0 < X.la1) {ε : ℝ} (hε : 0 < ε) :
    ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧
      LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ Module.finrank ℝ (IR I) / X.la1 + ε := by sorry
