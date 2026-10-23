-- Prove2me | Theorems.Thm_Paley11987Verified_CompactLabeling_card_internalEdges
-- name    : Paley11987Verified.CompactLabeling.card_internalEdges
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:24:14.053885+00:00
-- url     : https://prove2.me/theorems/b381dc55-07f9-471d-80c7-97d51a1e85e9
-- title:
--   Internal edges of a finite tournament
-- statement:
--   Let $V$ be a finite set and $R$ an irreflexive tournament relation: for distinct $x,y$, exactly one of $R(x,y)$ and $R(y,x)$ holds. For every subset $S\subseteq V$, the directed edges with both endpoints in $S$ satisfy
--   $$|\{(x,y)\in S^2:R(x,y)\}|=\binom{|S|}{2}.$$
--   This is the edge-counting identity used in the labeling estimates.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabelingGeometry, SHA256 8e8d158d09002e894af583f60555d6ea75055990434d8de7db7b8c105c681695; compact solution lines 75-110, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_000

set_option autoImplicit false
set_option Elab.async false
universe u_1

theorem Paley11987Verified.CompactLabeling.card_internalEdges :
∀ {V : Type u_1} [Fintype.{u_1} V] [DecidableEq.{u_1 + 1} V] (R : V → V → Prop),
  (∀ (x : V), Not (R x x)) →
    (∀ (x y : V), @Ne.{u_1 + 1} V x y → Iff (R x y) (Not (R y x))) →
      ∀ (S : Finset.{u_1} V),
        @Eq.{1} Nat (@Finset.card.{u_1} (Prod.{u_1, u_1} V V) (@ZL.internalEdges.{u_1} V R S))
          ((@Finset.card.{u_1} V S).choose (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by sorry
