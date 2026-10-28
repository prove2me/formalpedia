-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxNumeric_Endpoint22_seed_bounds3
-- name    : Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.seed_bounds3
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T02:51:14.588072+00:00
-- url     : https://prove2.me/theorems/b6b1b0ef-a05f-4871-845b-4a4aefd41da8
-- title:
--   seed bounds3 — Boolean sensitivity certificate
-- statement:
--   The following universally quantified assertion holds for the finite sets, Boolean families, tournament data, and profile coordinates defined in the imported interfaces. Each binder specifies the domain of its variable, and bracketed conditions specify finite or ordered structures.
--
--   $$
--   \operatorname{Endpoint22Hybrid.SeedBounds}\bigl(\operatorname{Endpoint22Records.records}, 3, \operatorname{Endpoint22.profile3}, \operatorname{Endpoint22.rawProfile3}, \operatorname{Endpoint22.aSeeds3}\bigr)
--   $$
--
--   Here $\mathbb B=\{\mathsf{false},\mathsf{true}\}$; $\mathcal P_{\mathrm{fin}}(X)$ denotes the finite subsets of $X$. Named functions and predicates refer to their definitions in the cited source. This result supplies the corresponding seed bounds3 step in the verified $22$-level sensitivity construction.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22SeedBounds3.lean, lines 38–80.

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData011
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData028
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData041
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData046
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData059
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData068
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData072
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData087
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData089
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData091
import Definitions.Def_Sensitivity213981Formal_Endpoint22AnnotatedData092
import Definitions.Def_Sensitivity213981Formal_Endpoint22CodeRecord
import Definitions.Def_Sensitivity213981Formal_Endpoint22CostValues
import Definitions.Def_Sensitivity213981Formal_Endpoint22EnvelopeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22HybridTransfer
import Definitions.Def_Sensitivity213981Formal_Endpoint22NibbleMask
import Definitions.Def_Sensitivity213981Formal_Endpoint22NumericData
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData
import Definitions.Def_Sensitivity213981Formal_Endpoint22SeedCover3
import Definitions.Def_Sensitivity213981Formal_Endpoint22StrictTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22SummaryData
import Definitions.Def_Sensitivity213981Formal_Endpoint22VariableCacheData1100
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Numeric
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
import Definitions.Def_Sensitivity213981Formal_RankCachedEvaluator
import Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
import Definitions.Def_Sensitivity213981Formal_RankCostExpressions
import Definitions.Def_Sensitivity213981Formal_RankFusedCoefficients
import Definitions.Def_Sensitivity213981Formal_RankPackedStrictCache
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch000
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch001
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch002
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch003
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch004
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch005
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch006
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch007
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch008
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch009
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch010
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch011
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch012
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch013
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch014
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch015
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch016
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch017
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch018
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch019
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch020
import Definitions.Def_Sensitivity213981Formal_UploadAnnotationBatch021
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean
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

theorem Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.seed_bounds3 :
Sensitivity213981Formal.ThreeBoundEndpoint22Hybrid.SeedBounds
  Sensitivity213981Formal.ThreeBoundEndpoint22Records.records
  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 3)
    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 3)))
  Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.profile3
  Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.rawProfile3
  Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.aSeeds3 := by sorry
