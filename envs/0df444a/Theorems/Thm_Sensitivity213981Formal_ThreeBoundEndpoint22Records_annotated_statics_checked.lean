-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Records_annotated_statics_checked
-- name    : Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated_statics_checked
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T23:01:59.608139+00:00
-- url     : https://prove2.me/theorems/e7e7a2a9-a3b6-4249-824e-040d374ed595
-- title:
--   The annotated coverage tree passes every static check
-- statement:
--   Let $T$ be the fixed annotated record tree of the $22$-level construction, let $K$ be its fixed array of packed key codes, and let $N$ be the number of keys. Then the recursive static checker accepts the entire tree:
--   \[T.\operatorname{checkStatics}(K.\operatorname{get},N)=\mathrm{true}.\]
--   The checker validates the tabulated key and row data at every leaf. This shared finite certificate is used by all subsequent arithmetic checks on the same tree.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22AnnotatedData.lean, lines 302–303.

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
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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

theorem Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated_statics_checked :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.checkStatics
    (Sensitivity213981Formal.ThreeBoundNumeric.NatTable.get
      Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCodes)
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.keyCount
    Sensitivity213981Formal.ThreeBoundEndpoint22Records.annotated)
  Bool.true := by sorry
