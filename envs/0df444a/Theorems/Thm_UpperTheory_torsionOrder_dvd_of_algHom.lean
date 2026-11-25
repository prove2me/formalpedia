-- Prove2me | Theorems.Thm_UpperTheory_torsionOrder_dvd_of_algHom
-- name    : UpperTheory.torsionOrder_dvd_of_algHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:14:40.899191+00:00
-- url     : https://prove2.me/theorems/bf5ccccd-25bd-41c0-8648-9e03e1cf474e
-- title:
--   Upper Theory: torsion Order dvd of alg Hom
-- statement:
--   The Upper Theory construction uses the torsion Order dvd of alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L32-L39

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
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
open UpperTheory
variable (E : Type) [Field E] [NumberField E]
variable {E}

theorem UpperTheory.torsionOrder_dvd_of_algHom (N : ℕ) (hN : Even N) (hN0 : 0 < N) (ψ : E →ₐ[ℚ] CyclotomicField N ℚ) :
    Units.torsionOrder E ∣ N := by sorry
