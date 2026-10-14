-- Prove2me | Theorems.Thm_ThreeSum_Histograms_correlation_histograms
-- name    : ThreeSum.Histograms.correlation_histograms
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:40:51.894363+00:00
-- url     : https://prove2.me/theorems/e5b86f2e-eb1f-487b-82c9-3de0a20b7473
-- title:
--   Weighted histogram correlation counts shifted pairs
-- statement:
--   Let $G$ be a finite abelian group, and let $I$ and $J$ be finite index sets. Give each $i\in I$ a key $\ell_i\in G$ and multiplicity $u_i\in\mathbb N$, and each $j\in J$ a key $r_j\in G$ and multiplicity $v_j\in\mathbb N$. Define the histograms $H_L(k)=\sum_{i\in I,\,\ell_i=k}u_i$ and $H_R(k)=\sum_{j\in J,\,r_j=k}v_j$. For every offset $d\in G$,
--
--   $$
--   \sum_{k\in G}H_R(k)H_L(k-d)
--   =\sum_{i\in I}\sum_{j\in J}\mathbf 1_{r_j-\ell_i=d}\,u_i v_j.
--   $$
--
--   Thus correlation gives the exact multiplicity of pairs with the prescribed key difference. The identity supports balancing the actual incidence histograms, including repeated keys and unequal multiplicities.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Histograms.lean#L37-L62

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2 u_4

theorem ThreeSum.Histograms.correlation_histograms : ∀ {ι : Type u_1} {τ : Type u_2} {G : Type u_4} [inst : AddCommGroup.{u_4} G] [inst_1 : Fintype.{u_4} G]
  [inst_2 : DecidableEq.{u_4 + 1} G] (I : Finset.{u_1} ι) (J : Finset.{u_2} τ) (left : ι → G) (right : τ → G)
  (weightL : ι → Nat) (weightR : τ → Nat) (d : G),
  @Eq.{1} Nat
    (@ThreeSum.Balancing.correlation.{u_4} G inst inst_1
      (@ThreeSum.Histograms.histogram.{u_2, u_4} τ G inst_2 J right weightR)
      (@ThreeSum.Histograms.histogram.{u_1, u_4} ι G inst_2 I left weightL) d)
    (@ThreeSum.Histograms.pairMass.{u_1, u_2, u_4} ι τ G inst inst_2 I J left right weightL weightR d) := by
  sorry
