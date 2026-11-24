-- Prove2me | Theorems.Thm_UpperTheory_MU_equiv_iff
-- name    : UpperTheory.MU.equiv_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:03.542828+00:00
-- url     : https://prove2.me/theorems/ae2fd9bf-1788-4fad-89fb-e170fa763a94
-- title:
--   MU: equiv iff
-- statement:
--   The MU construction uses the equiv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdNegOneZpow.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdNegOneZpow.lean#L56-L58

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory
variable {E K K' : Type} [Field E] [Field K] [Field K'] {ι ι' : Type} [Fintype ι] [Fintype ι']
open UpperTheory.MU
variable {φ : ι → E →+* K} {e e' : ι → ℤ}

theorem UpperTheory.MU.equiv_iff (s : ι' ≃ ι) : MU (fun i => φ (s i)) (fun i => e (s i)) ↔ MU φ e := by sorry
