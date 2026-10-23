-- Prove2me | Theorems.Thm_Paley11987Verified_SensitivityCampaign_paley11987_actual_seeds
-- name    : Paley11987Verified.SensitivityCampaign.paley11987_actual_seeds
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T05:53:35.912359+00:00
-- url     : https://prove2.me/theorems/ca79b303-3ea1-42c0-a66b-a150fcd77ce3
-- title:
--   Paley11987 sensitivity and block-sensitivity witnesses
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   For every natural $m$, there exists a Boolean function $f_m$ on a finite set of coordinates such that
--   $$16^m\le s(f_m)\le230508375206254\cdot45238253^m,\qquad
--   11987^{4m}\le bs(f_m).$$
--   These are unconditional witnesses from the selected Paley tournament, its capped labeling, and the checked four-stage numerical certificate. They provide the finite-function estimates underlying the claimed exponent.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module Compact11987Solution, SHA256 4e34f4b0ca0260fb81b87e0bc4e440b7dfbac780eb68164a31f47e5847a91c2a; compact solution lines 17462-17466, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_054

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.SensitivityCampaign.paley11987_actual_seeds :
ZP.ActualSeedStatement := by sorry
