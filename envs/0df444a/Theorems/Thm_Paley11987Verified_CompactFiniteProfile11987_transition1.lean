-- Prove2me | Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_transition1
-- name    : Paley11987Verified.CompactFiniteProfile11987.transition1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T05:24:54.105308+00:00
-- url     : https://prove2.me/theorems/939966e3-3206-4112-b542-3e7c74dcc701
-- title:
--   Finite profile transition 1 to 2
-- statement:
--   Let $v_1$ and $v_2$ be the fixed natural-valued profile tables, and let $r_1$ be the recorded recipe. All five transfer coefficients are dominated by the next profile:
--   $$\operatorname{rawA}(v_1,r_1;i,j)\le A_{v_2}(i,j),\quad
--   \operatorname{rawB}(v_1,r_1;i,j)\le B_{v_2}(i,j),$$
--   $$\operatorname{rawM}(v_1,r_1;i,j)\le M_{v_2}(i,j),\quad
--   \operatorname{rawP}(v_1,r_1;j,l)\le P_{v_2}(j,l),\quad
--   \operatorname{rawD}(v_1,r_1;i,j,l)\le D_{v_2}(i,j,l).$$
--   The A and B inequalities hold for $0\le i\le j<20$; M additionally requires $j+1<20$; P holds for $0\le j<l<20$; and D for $0\le i\le j<l<20$. This is a closed, finite transition certificate for the specified tables and recipe.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfile11987CompactTransition1, SHA256 9f31eb1287a5d3a56dd38ada627c876672d7bcd14ba779d8d830d493631294e4; compact solution lines 14270-14275, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

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
import Definitions.Def_Paley11987Support_047

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactFiniteProfile11987.transition1 :
ZP.TransitionCertificate ZP.stage1 ZP.recipe1 ZP.stage2 := by sorry
