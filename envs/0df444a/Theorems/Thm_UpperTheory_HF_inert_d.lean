-- Prove2me | Theorems.Thm_UpperTheory_HF_inert_d
-- name    : UpperTheory.HF.inert_d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:28.911113+00:00
-- url     : https://prove2.me/theorems/567c7492-d501-4557-a64b-e4efcc7fab9a
-- title:
--   HF: inert d
-- statement:
--   The HF construction uses the inert d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/InertD.lean#L12-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/InertD.lean#L12-L64

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTameWild
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_InertD
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

theorem UpperTheory.HF.inert_d :
    ∀ {φ : Frame} (H : HostAx φ), H.inertG H.d = Subgroup.zpowers φ.iod ∧ H.el H.d = 2 ∧ H.vdH H.d = 1 / 2 ∧ H.sl H.d = 1 ∧ H.d ∈ H.ram ∧ 2 ∈ H.ram ∧ H.condE.factorization H.d = 1 := by sorry
