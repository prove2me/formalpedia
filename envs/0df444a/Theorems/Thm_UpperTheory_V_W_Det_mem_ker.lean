-- Prove2me | Theorems.Thm_UpperTheory_V_W_Det_mem_ker
-- name    : UpperTheory.V.W.Det.mem_ker
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:23:09.55848+00:00
-- url     : https://prove2.me/theorems/07500795-5132-4829-bf1c-8177d3b167c5
-- title:
--   Det: mem ker
-- statement:
--   The Det construction uses the mem ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebraHeight/OfDetToDet.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebraHeight/OfDetToDet.lean#L46-L47

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
open UpperTheory.V.W.Det
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

theorem UpperTheory.V.W.Det.mem_ker {x : E} : x ∈ D.ker ↔ ∀ (S : Type) [CommRing S] [Algebra A S] (y u v : S ⊗[A] E),
    D.D S (y + u * (1 ⊗ₜ x) * v) = D.D S y := by sorry
