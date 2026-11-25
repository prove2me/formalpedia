-- Prove2me | Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_isMu_iff_pow
-- name    : UpperTheory.HF.Formalism.HC.HostRaw.isMu_iff_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:13:50.937054+00:00
-- url     : https://prove2.me/theorems/ce0cb2d7-87c6-4588-b70f-c87294407ce1
-- title:
--   Host Raw: is Mu iff pow
-- statement:
--   The Host Raw construction uses the is Mu iff pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/MuDefs.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/MuDefs.lean#L32-L39

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MuDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open UpperTheory UpperTheory.HF UpperTheory.HF.Formalism UpperTheory.HF.Formalism.HC UpperTheory.HF.Formalism.HC.HostRaw
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)

theorem UpperTheory.HF.Formalism.HC.HostRaw.isMu_iff_pow (x : H.E) : H.IsMu x ↔ ∃ k : ℕ, x = H.muGen ^ k := by sorry
