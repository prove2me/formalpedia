-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_eq_of_le_ddd9ed9a76c6
-- name    : P2M_GroundTheory_Heights__Heights_height_eq_of_le_ddd9ed9a76c6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:04:17.294925+00:00
-- url     : https://prove2.me/theorems/826e2a7c-29d7-4ad4-9a91-5658010d1bc6
-- title:
--   P2 M Ground Theory Heights  Heights height eq of le ddd9ed9a76c6: P2 M Ground Theory Heights  Heights height eq of le ddd9ed9a76c6
-- statement:
--   The P2 M Ground Theory Heights  Heights height eq of le ddd9ed9a76c6 construction uses the P2 M Ground Theory Heights  Heights height eq of le ddd9ed9a76c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L194-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L194-L219

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Module
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_height_eq_of_le_ddd9ed9a76c6 (A : HermLine n) {x : Cone n (AlgebraicClosure ℚ)} (hx0 : BlockNonzero x)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L] (hx : ∀ k i, x k i ∈ L) :
    height A x = ((finrank ℚ L : ℝ))⁻¹ *
      (∑ᶠ w : FinitePlace L, finiteTerm A w (coordIn L x hx) +
        ∑ σ : L →+* ℂ, Real.log (A.metric fun k i ↦ σ (coordIn L x hx k i))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«height_eq_of_le» := P2M_GroundTheory_Heights__Heights_height_eq_of_le_ddd9ed9a76c6
