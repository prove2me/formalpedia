-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Records_converted_checked23
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Records.converted_checked23
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T23:57:56.112715+00:00
-- url     : https://prove2.me/theorems/cf01d232-c15b-4120-ae6e-494ed64902c3
-- title:
--   converted checked23 — Boolean sensitivity certificate
-- statement:
--   For every record in conversion batch 023, the converted-cost predicate holds. In particular, the recorded admissible profile transformations preserve the required converted-coordinate upper bound. All records and numerical constants are fixed by the imported tables; there are no free numerical hypotheses. This finite certificate supplies one batch of the converted-cost verification for the $22$-level sensitivity construction.
--
--   $$
--   \bigl(\operatorname{ClosureCertificate.checkInterval}\bigl(\operatorname{Endpoint22Records.summaryCheckAt}, 2944, 3072\bigr) = \mathsf{true}\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding converted checked23 step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ConvertedChecks023.lean, lines 13–14.

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Endpoint22SummaryData
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
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

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Records.converted_checked23 :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.checkInterval
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.summaryCheckAt
    (@OfNat.ofNat.{0} Nat (nat_lit 2944) (instOfNatNat (nat_lit 2944)))
    (@OfNat.ofNat.{0} Nat (nat_lit 3072) (instOfNatNat (nat_lit 3072))))
  Bool.true := by sorry
