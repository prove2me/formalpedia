-- Prove2me | Theorems.Thm_UpperTheory_HF_vd_formula
-- name    : UpperTheory.HF.vd_formula
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:03:45.411807+00:00
-- url     : https://prove2.me/theorems/cb2a4338-5b26-4a5d-bc09-ac507a9072fa
-- title:
--   HF: vd formula
-- statement:
--   The HF construction uses the vd formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/VdFormula.lean#L57-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/VdFormula.lean#L57-L88

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RhoArt
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogPrimeIndep
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
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

theorem UpperTheory.HF.vd_formula :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → H.vdH l = ∑ j ∈ Finset.range (H.condN.factorization l), (1 - 1 / (Nat.card (H.imgOne (ordCompl[l] H.condN * l ^ j)) : ℝ)) := by sorry
