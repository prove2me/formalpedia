-- Prove2me | Theorems.Thm_UpperTheory_MU_aut
-- name    : UpperTheory.MU.aut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:57.533732+00:00
-- url     : https://prove2.me/theorems/05d67130-d069-4f55-95b2-77bd77106684
-- title:
--   MU: aut
-- statement:
--   The MU construction uses the aut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdNegOneZpow.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdNegOneZpow.lean#L60-L62

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

theorem UpperTheory.MU.aut (h : MU φ e) (g : E →+* E) : MU (fun i => (φ i).comp g) e := by sorry
