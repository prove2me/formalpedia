-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_multidegree_piece_iff
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mem_multidegree_piece_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:57.873415+00:00
-- url     : https://prove2.me/theorems/2202f3e8-a954-4393-86c3-bf26648fe42e
-- title:
--   Arakelov Geometry: mem multidegree piece iff
-- statement:
--   The Arakelov Geometry construction uses the mem multidegree piece iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CardPieceIrrelevantIdeal.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CardPieceIrrelevantIdeal.lean#L11-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mem_multidegree_piece_iff {W : Ideal (MRing ι)} {a : K → ℕ} {y : MRing ι ⧸ W} :
    y ∈ mPiece W a ↔ ∃ h, IsMultiHomog h a ∧ Ideal.Quotient.mk W h = y := by sorry
