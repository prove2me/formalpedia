-- Prove2me | Theorems.Thm_UpperTheory_HF_ram_eq
-- name    : UpperTheory.HF.ram_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:27:52.866034+00:00
-- url     : https://prove2.me/theorems/1cf7c89a-1d02-4973-ad31-db8bb13c6d65
-- title:
--   HF: ram eq
-- statement:
--   The HF construction uses the ram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/RamEq.lean#L76-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/RamEq.lean#L76-L174

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_InertD
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_inertQ
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondESpec
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RamEq
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

theorem UpperTheory.HF.ram_eq :
    ∀ {φ : Frame} (H : HostAx φ), (∀ l, l ∈ H.ram ↔ l ∈ H.smallR ∨ (l = H.q ∧ H.q ∈ H.ram) ∨ l = H.d) ∧ 2 ∈ H.smallR ∧ H.ram = H.condE.primeFactors ∧ H.condE = H.QSc * (if H.q ∈ H.ram then H.q else 1) * H.d ∧ H.QSc ∣ H.QS ∧ 2 ^ (φ.e + 2) ∣ H.QSc ∧ (∀ l ∈ H.smallR, H.sl l = H.condE.factorization l) ∧ (∀ l ∈ H.ramI, l ∣ H.QS * H.q) := by sorry
