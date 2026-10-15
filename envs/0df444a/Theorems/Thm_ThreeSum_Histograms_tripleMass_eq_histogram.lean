-- Prove2me | Theorems.Thm_ThreeSum_Histograms_tripleMass_eq_histogram
-- name    : ThreeSum.Histograms.tripleMass_eq_histogram
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:46:02.752022+00:00
-- url     : https://prove2.me/theorems/3b5f7a76-9058-4ea3-ab33-e488dcfa1036
-- title:
--   Weighted triple mass is a histogram correlation
-- statement:
--   Let $G$ be a finite abelian group with decidable equality. Let $A,B,C$ be finite index sets with keys $a_i,b_j,c_k\in G$ and natural weights $u_i,v_j,w_k$. Define $H_B(z)=\sum_{j\in B:b_j=z}v_j$ and $H_C(z)=\sum_{k\in C:c_k=z}w_k$, and let $\operatorname{Corr}(H_C,H_B)(d)=\sum_{z\in G}H_C(z)H_B(z-d)$. Then
--
--   $$\sum_{\substack{i\in A,j\in B,k\in C\\a_i+b_j=c_k}}u_i v_j w_k=\sum_{i\in A}u_i\operatorname{Corr}(H_C,H_B)(a_i).$$
--
--   A single B/C correlation therefore supports all A-key queries while retaining every multiplicity, including repeated keys.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Histograms.lean#L91-L113

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
import Theorems.Thm_ThreeSum_Histograms_correlation_histograms


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2 u_3 u_4

theorem ThreeSum.Histograms.tripleMass_eq_histogram : ∀ {ι : Type u_1} {τ : Type u_2} {ν : Type u_3} {G : Type u_4} [inst : AddCommGroup.{u_4} G] [inst_1 : Fintype.{u_4} G]
  [inst_2 : DecidableEq.{u_4 + 1} G] (A : Finset.{u_1} ι) (B : Finset.{u_2} τ) (C : Finset.{u_3} ν) (a : ι → G)
  (b : τ → G) (c : ν → G) (wa : ι → Nat) (wb : τ → Nat) (wc : ν → Nat),
  @Eq.{1} Nat (@ThreeSum.Histograms.tripleMass.{u_1, u_2, u_3, u_4} ι τ ν G inst inst_2 A B C a b c wa wb wc)
    (∑ i ∈ A,
      @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (wa i)
        (@ThreeSum.Balancing.correlation.{u_4} G inst inst_1
          (@ThreeSum.Histograms.histogram.{u_3, u_4} ν G inst_2 C c wc)
          (@ThreeSum.Histograms.histogram.{u_2, u_4} τ G inst_2 B b wb) (a i))) := by
  sorry
