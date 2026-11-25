-- Prove2me | Theorems.Thm_UpperTheory_HF_imgOne_gcd
-- name    : UpperTheory.HF.imgOne_gcd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:15.063025+00:00
-- url     : https://prove2.me/theorems/3fec7a1b-e7fb-4aaa-b6d5-4e1368048edd
-- title:
--   HF: img One gcd
-- statement:
--   The HF construction uses the img One gcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/ImgOneGcd.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/ImgOneGcd.lean#L9-L22

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_ImgOneGcd
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

theorem UpperTheory.HF.imgOne_gcd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ H.condN → g ∣ H.condN → H.imgOne (Nat.gcd f g) = H.imgOne f ⊔ H.imgOne g := by sorry
