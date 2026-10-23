-- Prove2me | Theorems.Thm_Paley11987Verified_CompactLabeling11987_exists_joint_exclusions
-- name    : Paley11987Verified.CompactLabeling11987.exists_joint_exclusions
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:34:24.233725+00:00
-- url     : https://prove2.me/theorems/20c133be-481b-4f31-9b54-db2fd9c634dd
-- title:
--   A joint exclusion labeling on 11987 vertices
-- statement:
--   Let $R$ be an irreflexive tournament on $11987$ vertices, with indegree and outdegree $5993$ and common in- and out-neighbor counts $2996$ for distinct vertices. There is a binary labeling of ordered vertex pairs satisfying the entire recorded exclusion system:
--   $$\exists\ell:V\times V\to\{0,1\},\qquad \mathrm{JointExclusions}(R,\ell).$$
--   The exclusion system is the finite collection of ordinary, marked, source, and two-dominator bad-event exclusions defined in the accompanying interface. Its existence supplies the labeling used in the Boolean transfer construction.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabeling11987Joint, SHA256 f43609b027676880501481b9bb66e7b84f6e7ae90b71f42a2ecfa8241cd76fcf; compact solution lines 3967-3991, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Paley11987Support_018

set_option autoImplicit false
set_option Elab.async false
universe u_1

theorem Paley11987Verified.CompactLabeling11987.exists_joint_exclusions :
∀ {V : Type u_1} [inst : Fintype.{u_1} V] [inst_1 : DecidableEq.{u_1 + 1} V] (R : V → V → Prop),
  @Eq.{1} Nat (@Fintype.card.{u_1} V inst) CompactLabeling11987.N →
    (∀ (x : V), Not (R x x)) →
      (∀ (x y : V), @Ne.{u_1 + 1} V x y → Iff (R x y) (Not (R y x))) →
        (∀ (x : V),
            @Eq.{1} Nat (@Finset.card.{u_1} V (@ZL.outOn.{u_1} V R (@Finset.univ.{u_1} V inst) x))
              CompactLabeling11987.degree) →
          (∀ (x : V),
              @Eq.{1} Nat (@Finset.card.{u_1} V (@ZL.inOn.{u_1} V R (@Finset.univ.{u_1} V inst) x))
                CompactLabeling11987.degree) →
            (∀ (x y : V),
                @Ne.{u_1 + 1} V x y →
                  @Eq.{1} Nat
                    (@Finset.card.{u_1} V
                      (@Finset.filter.{u_1} V (fun z => And (R z x) (R z y))
                        (fun a =>
                          @instDecidableAnd (R a x) (R a y) (Classical.propDecidable (R a x))
                            (Classical.propDecidable (R a y)))
                        (@Finset.univ.{u_1} V inst)))
                    CompactLabeling11987.common) →
              (∀ (x y : V),
                  @Ne.{u_1 + 1} V x y →
                    @Eq.{1} Nat
                      (@Finset.card.{u_1} V
                        (@Finset.filter.{u_1} V (fun z => And (R x z) (R y z))
                          (fun a =>
                            @instDecidableAnd (R x a) (R y a) (Classical.propDecidable (R x a))
                              (Classical.propDecidable (R y a)))
                          (@Finset.univ.{u_1} V inst)))
                      CompactLabeling11987.common) →
                @Exists.{u_1 + 1}
                  (Prod.{u_1, u_1} V V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun ell =>
                  @CompactLabeling11987.JointExclusions.{u_1} V inst inst_1 R ell := by sorry
