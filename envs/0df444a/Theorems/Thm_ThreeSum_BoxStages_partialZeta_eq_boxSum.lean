-- Prove2me | Theorems.Thm_ThreeSum_BoxStages_partialZeta_eq_boxSum
-- name    : ThreeSum.BoxStages.partialZeta_eq_boxSum
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:38:33.151191+00:00
-- url     : https://prove2.me/theorems/dde1876a-b33e-4f91-95fd-2c35e64241e8
-- title:
--   A partial zeta transform is a box sum
-- statement:
--   Let $L\in\mathbb N$, let $w$ be an integer-valued function on subsets of $\{0,\ldots,L-1\}$, and let $F,P$ be subsets of this ground set. Define the partial zeta transform by $Z_Pw(F)=\sum_{X\subseteq F\cap P}w((F\setminus P)\cup X)$. Then
--
--   $$
--   Z_Pw(F)=\sum_{F\setminus P\subseteq S\subseteq F}w(S)
--   =\operatorname{boxSum}(F,F\cap P,w).
--   $$
--
--   Thus the processed coordinates are exactly the free coordinates of the box, while unprocessed flagged coordinates remain required. This bridges the stored transform invariant and the sparse-box query specification.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BoxStages.lean#L85-L133

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.BoxStages.partialZeta_eq_boxSum : ∀ {L : Nat} (weight : Finset.{0} (Fin L) → Int) (flags processed : Finset.{0} (Fin L)),
  @Eq.{1} Int (@ThreeSum.Subset.partialZeta.{0} (Fin L) (instDecidableEqFin L) processed weight flags)
    (@ThreeSum.SparseBoxes.boxSum.{0} (Fin L) (@Fin.instLinearOrder L) flags
      (@Inter.inter.{0} (Finset.{0} (Fin L)) (@Finset.instInter.{0} (Fin L) (instDecidableEqFin L)) flags processed)
      weight) := by
  sorry
