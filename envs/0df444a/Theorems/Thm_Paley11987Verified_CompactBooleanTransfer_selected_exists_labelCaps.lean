-- Prove2me | Theorems.Thm_Paley11987Verified_CompactBooleanTransfer_selected_exists_labelCaps
-- name    : Paley11987Verified.CompactBooleanTransfer.selected_exists_labelCaps
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T04:45:19.221969+00:00
-- url     : https://prove2.me/theorems/f75a36e8-64fe-42c3-865b-5a45d7d8d98f
-- title:
--   A labeling with all transfer caps on the selected Paley tournament
-- statement:
--   Let $T_{11987}$ be the selected tournament on $\{0,\ldots,11986\}$ obtained from the Paley core. There exists a binary labeling of ordered vertex pairs satisfying every cap in the Boolean transfer interface:
--   $$\exists\ell:\{0,\ldots,11986\}^2\to\{0,1\},\qquad \operatorname{LabelCaps}(T_{11987},\ell).$$
--   These caps control ordinary and marked candidates, source configurations, and double-dominator configurations. This supplies the labeled tournament required by the finite profile construction.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabeling11987Caps, SHA256 627efd0148d95d08968625d5fe7372e8957ba59182ebb75694fb0cc8c5b48ef3; compact solution lines 7859-7867, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_035

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactBooleanTransfer.selected_exists_labelCaps :
@Exists.{1}
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))) →
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  fun label =>
  @ZT.LabelCaps (@OfNat.ofNat.{0} Nat (nat_lit 11987) (instOfNatNat (nat_lit 11987))) ZT.selectedTournament label := by sorry
