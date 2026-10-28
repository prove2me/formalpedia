-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundWitness_blockSensitivity_lower_of_indexed_blocks
-- name    : Sensitivity213981Formal.ThreeBoundWitness.blockSensitivity_lower_of_indexed_blocks
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:34:25.708723+00:00
-- url     : https://prove2.me/theorems/4e662e5d-d97a-431c-86f7-f4195bd9f82b
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
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; WitnessLifting.lean, lines 278–316.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundWitness.blockSensitivity_lower_of_indexed_blocks :
∀ {I : Type} [inst : Fintype.{0} I] {A : Type} [inst_1 : Fintype.{0} A] (f : (I → Bool) → Bool) (x : I → Bool)
  (B : A → Finset.{0} I) (hne : ∀ (a : A), @Finset.Nonempty.{0} I (B a))
  (hdis :
    ∀ (a b : A),
      @Ne.{1} A a b →
        @Disjoint.{0} (Finset.{0} I) (@Finset.instPartialOrder.{0} I) (@Finset.instOrderBot.{0} I) (B a) (B b))
  (hflip : ∀ (a : A), @Ne.{1} Bool (f (@OAI.Paper320.flip I x (B a))) (f x)),
  @LE.le.{0} Nat instLENat (@Fintype.card.{0} A inst_1) (@OAI.Paper320.blockSensitivity I inst f) := by sorry
