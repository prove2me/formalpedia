-- Prove2me | Theorems.Thm_UpperTheory_HF_vd_two
-- name    : UpperTheory.HF.vd_two
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:23.749224+00:00
-- url     : https://prove2.me/theorems/c6b901b2-1f40-4aa4-852b-aa88a027e846
-- title:
--   HF: vd two
-- statement:
--   The HF construction uses the vd two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/VdTwo.lean#L53-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/VdTwo.lean#L53-L87

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RhoArt
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.vd_two :
    ∀ {φ : Frame} (H : HostAx φ), (φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ)) ≤ H.vdH 2 ∧ 11 / 4 ≤ H.vdH 2 ∧ 4 + 2 * H.vdH 2 ≤ 2 + 3 * H.vdH 2 := by sorry
