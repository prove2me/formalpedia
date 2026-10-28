-- Prove2me | Theorems.Thm_ThreeBoundWitness_blockSensitivity_lower_of_indexed_blocks
-- name    : ThreeBoundWitness.blockSensitivity_lower_of_indexed_blocks
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:37:48.250006+00:00
-- url     : https://prove2.me/theorems/1dc42845-b17d-40bc-869e-325b2233e606
-- title:
--   Indexed disjoint sensitive blocks give a block-sensitivity lower bound
-- statement:
--   Let \(f:\{0,1\}^{I}\to\{0,1\}\) be a Boolean function on a finite coordinate type, and let \(x\) be an input. Suppose a finite index type \(A\) supplies nonempty, pairwise disjoint blocks \(B_a\subseteq I\) such that
--   \[
--   f(x^{B_a})\ne f(x)\qquad(a\in A),
--   \]
--   where \(x^{B_a}\) means flipping every coordinate in \(B_a\). Then
--   \[
--   bs(f)\ge |A|.
--   \]
--   This connects the explicit recursive block witnesses to the campaign's definition of block sensitivity.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, WitnessLifting, lines 278–316; source SHA256 3de5b42744f1a0f912bff6a7825dc8a21c88ce1eeb9e3364123000d6bca68bcc.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ThreeBoundWitness
end ThreeBoundWitness
open ThreeBoundWitness
open OAI.Paper320
variable {L I V : Type}

theorem ThreeBoundWitness.blockSensitivity_lower_of_indexed_blocks [Fintype I] {A : Type} [Fintype A]
    (f : (I → Bool) → Bool) (x : I → Bool) (B : A → Finset I)
    (hne : ∀ a, (B a).Nonempty)
    (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (hflip : ∀ a, f (flip x (B a)) ≠ f x) :
    Fintype.card A ≤ blockSensitivity f := by sorry
