-- Prove2me | Theorems.Thm_P2M_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_finrank_pos__df67f6332271
-- name    : P2M_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_finrank_pos__df67f6332271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:52.188429+00:00
-- url     : https://prove2.me/theorems/b5e4bf13-932c-433c-bcfa-06ab2193f80f
-- title:
--   P2 M Formalism Branching Determinant Cap Orthogonal Sum Alt finrank pos  df67f6332271: P2 M Formalism Branching Determinant Cap Orthogonal Sum Alt finrank pos  df67f6332271
-- statement:
--   The P2 M Formalism Branching Determinant Cap Orthogonal Sum Alt finrank pos  df67f6332271 construction uses the P2 M Formalism Branching Determinant Cap Orthogonal Sum Alt finrank pos  df67f6332271 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L39-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L39-L39

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.OrthogonalSumAlt
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem P2M_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_finrank_pos__df67f6332271 : 0 < Module.finrank ℚ K := by sorry

alias «Formalism».«BranchingDeterminantCap».«OrthogonalSumAlt».«finrank_pos'» := P2M_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_finrank_pos__df67f6332271
