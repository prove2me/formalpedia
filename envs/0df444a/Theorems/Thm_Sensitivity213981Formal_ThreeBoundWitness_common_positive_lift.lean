-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundWitness_common_positive_lift
-- name    : Sensitivity213981Formal.ThreeBoundWitness.common_positive_lift
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:35:07.837113+00:00
-- url     : https://prove2.me/theorems/7101c66e-633c-4926-990b-5af08a8edd86
-- title:
--   One recursive stage doubles common sensitive-bit witnesses
-- statement:
--   Let a Boolean family \(F\) have a common rejected input \(z\), a common accepted input \(p\), and distinct coordinates \(e(a)\), indexed by a type \(A\), whose individual flips make every level reject \(p\). Let a recursive stage accept a pair of common accepted children at defect zero and reject whenever one of its two children is rejected at every level. For any vertex \(v\), the parent family has a common accepted input \(p'\) with an embedding
--   \[
--   e':\{\mathrm{false},\mathrm{true}\}\times A\hookrightarrow (V\times\mathrm{Bool})\times I
--   \]
--   such that flipping any coordinate \(e'(b,a)\) makes every parent level reject. This supplies the factor of two in the sensitivity witness growth.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; WitnessLifting.lean, lines 162–185.

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

theorem Sensitivity213981Formal.ThreeBoundWitness.common_positive_lift :
∀ {L I V : Type} [inst : Fintype.{0} V] {A : Type} (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V)
  (F : L → (I → Bool) → Bool) (z p : I → Bool) (hz : ∀ (l : L), @Eq.{1} Bool (F l z) Bool.false)
  (hp : ∀ (l : L), @Eq.{1} Bool (F l p) Bool.true) (e : Function.Embedding.{1, 1} A I)
  (he :
    ∀ (a : A) (l : L),
      @Eq.{1} Bool
        (F l
          (@OAI.Paper320.flip I p
            (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I)
              (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} A I) A (fun (x : A) => I)
                (@Function.instFunLikeEmbedding.{1, 1} A I) e a))))
        Bool.false)
  (haccept :
    ∀ (l : L) (x y : I → Bool),
      (∀ (a : L), @Eq.{1} Bool (F a x) Bool.true) →
        (∀ (a : L), @Eq.{1} Bool (F a y) Bool.true) →
          @Eq.{1} Bool
            (@Sensitivity213981Formal.ThreeBoundWitness.Stage.target L I V S l
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x y)
            Bool.true)
  (hreject :
    ∀ (l : L) (d : Nat) (x y : I → Bool),
      Or (∀ (a : L), @Eq.{1} Bool (F a x) Bool.false) (∀ (a : L), @Eq.{1} Bool (F a y) Bool.false) →
        @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.target L I V S l d x y) Bool.false)
  (v : V),
  @Exists.{1} (Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) fun (p' : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) =>
    @Exists.{1} (Function.Embedding.{1, 1} (Prod.{0, 0} Bool A) (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      fun (e' : Function.Embedding.{1, 1} (Prod.{0, 0} Bool A) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)) =>
      And (∀ (l : L), @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst S F l p') Bool.true)
        (∀ (a : Prod.{0, 0} Bool A) (l : L),
          @Eq.{1} Bool
            (@Sensitivity213981Formal.ThreeBoundWitness.parent L I V inst S F l
              (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) p'
                (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
                  (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
                  (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
                  (@DFunLike.coe.{1, 1, 1}
                    (Function.Embedding.{1, 1} (Prod.{0, 0} Bool A) (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
                    (Prod.{0, 0} Bool A) (fun (x : Prod.{0, 0} Bool A) => Prod.{0, 0} (Prod.{0, 0} V Bool) I)
                    (@Function.instFunLikeEmbedding.{1, 1} (Prod.{0, 0} Bool A) (Prod.{0, 0} (Prod.{0, 0} V Bool) I)) e'
                    a))))
            Bool.false) := by sorry
