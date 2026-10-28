-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_bulk_block_1100_5
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bulk_block_1100_5
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T00:43:25.953418+00:00
-- url     : https://prove2.me/theorems/648ac405-1b0a-49dd-999a-863d9dbd8c46
-- title:
--   bulk block 1100 5 — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \bigl(\operatorname{Tree.fastCheck}\bigl(\operatorname{Endpoint22.deny1100}, 3, \operatorname{Endpoint22.values1100}, \operatorname{Endpoint22.bound1100}, \operatorname{Endpoint22Records.annotated5}\bigr) = \mathsf{true}\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding bulk block 1100 5 step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22Bulk1100Block005.lean, lines 38–55.

import Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictPacked
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22VariableCacheData1100
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
import Definitions.Def_Sensitivity213981Formal_RankPackedStrictCache
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch001
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bulk_block_1100_5 :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.deny1100
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.values1100
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.bound1100
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated5)
  Bool.true := by sorry
