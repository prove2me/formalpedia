-- Prove2me | Theorems.Thm_UpperTheory_V_W_toT_ofT
-- name    : UpperTheory.V.W.toT_ofT
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:04.727816+00:00
-- url     : https://prove2.me/theorems/0e555a92-9fe2-48ed-8249-7bfb2b2e67b2
-- title:
--   W: to T of T
-- statement:
--   The W construction uses the to T of T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebraHeight/OfDetToDet.lean#L167-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebraHeight/OfDetToDet.lean#L167-L177

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnopSMul
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebraHeight_OfDetToDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing
open UpperTheory UpperTheory.V UpperTheory.V.W
variable (A G S : Type) [CommRing A] [Group G] [CommRing S] [Algebra A S]
variable {A G S}

theorem UpperTheory.V.W.toT_ofT (x : S ⊗[A] MonoidAlgebra A G) : toT A G S (ofT A G S x) = x := by sorry
