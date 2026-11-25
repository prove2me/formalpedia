-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_I_snoc_triv_8bf95163c347
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_I_snoc_triv_8bf95163c347
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:03.127809+00:00
-- url     : https://prove2.me/theorems/ac2e3889-4864-4c35-bafe-1739b8ed9401
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux I snoc triv 8bf95163c347: P2 M Ground Theory Heights  Heights Inter Diag RAux I snoc triv 8bf95163c347
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux I snoc triv 8bf95163c347 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux I snoc triv 8bf95163c347 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L50-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L50-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_I_snoc_triv_8bf95163c347 {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} {A : HermLine ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (ha : A.a = 0) (h1 : ∀ z ∈ mcPts P, A.h z = 1) :
    I P (n + 1) (Fin.snoc L A) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«I_snoc_triv» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_I_snoc_triv_8bf95163c347
