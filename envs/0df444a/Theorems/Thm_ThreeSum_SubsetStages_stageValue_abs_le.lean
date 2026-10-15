-- Prove2me | Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le
-- name    : ThreeSum.SubsetStages.stageValue_abs_le
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:43:58.53521+00:00
-- url     : https://prove2.me/theorems/cc96237b-037d-42ff-9c12-b5845f810101
-- title:
--   Magnitude bound for every suffix zeta stage
-- statement:
--   Let $L,c,U\in\mathbb N$ and let $f$ assign an integer to every subset of $\{0,\ldots,L-1\}$. Suppose $|f(S)|\le U$ for all $|S|\le c$. Let $P_j=\{L-j,\ldots,L-1\}$ for $j\le L$, and define $Z_jf(S)=\sum_{X\subseteq S\cap P_j}f((S\setminus P_j)\cup X)$. Then
--
--   $$
--   \forall j\le L\ \forall S\text{ with }|S|\le c,\qquad |Z_jf(S)|\le2^jU.
--   $$
--
--   This bounds every intermediate suffix-transform value from the original input bound, so intermediate magnitude bounds need not be additional assumptions in the stored-table specification.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SubsetStages.lean#L64-L88

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Subset_partialZeta_insert


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.SubsetStages.stageValue_abs_le : ∀ {L cut U : Nat} (f : Finset.{0} (Fin L) → Int)
  (hf :
    ∀ (S : Finset.{0} (Fin L)),
      @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (f S))
          (@Nat.cast.{0} Int instNatCastInt U))
  (j : Nat),
  @LE.le.{0} Nat instLENat j L →
    ∀ (S : Finset.{0} (Fin L)),
      @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup (@ThreeSum.SubsetStages.stageValue L f j S))
          (@Nat.cast.{0} Int instNatCastInt
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)
              U)) := by
  sorry
