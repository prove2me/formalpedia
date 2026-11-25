-- Prove2me | Theorems.Thm_P2M_RH_Formalism_HC_HostRaw_ordCompl_q_2735571a88a0a567
-- name    : P2M_RH_Formalism_HC_HostRaw_ordCompl_q_2735571a88a0a567
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:14.401093+00:00
-- url     : https://prove2.me/theorems/324a42ae-3075-4e01-93fd-3e5f07b4da3c
-- title:
--   P2 M RH Formalism HC Host Raw ord Compl q 2735571a88a0a567: P2 M RH Formalism HC Host Raw ord Compl q 2735571a88a0a567
-- statement:
--   The P2 M RH Formalism HC Host Raw ord Compl q 2735571a88a0a567 construction uses the P2 M RH Formalism HC Host Raw ord Compl q 2735571a88a0a567 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/CycImage.lean#L109-L111

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_HC_D7_ordCompl_q

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)

theorem P2M_RH_Formalism_HC_HostRaw_ordCompl_q_2735571a88a0a567 : ordCompl[H.q] H.condN = H.QS * H.d := by sorry

alias «Formalism».«HC».«HostRaw».«ordCompl_q» := P2M_RH_Formalism_HC_HostRaw_ordCompl_q_2735571a88a0a567
