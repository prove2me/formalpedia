-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_disjoint_iff_260247d60a12
-- name    : P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_disjoint_iff_260247d60a12
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:25.734654+00:00
-- url     : https://prove2.me/theorems/021678c4-e6ad-543d-b758-5645e1827981
-- title:
--   P2 M Ground Theory Heights  Heights Chart Max Ideals disjoint iff 260247d60a12: P2 M Ground Theory Heights  Heights Chart Max Ideals disjoint iff 260247d60a12
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Max Ideals disjoint iff 260247d60a12 construction uses the P2 M Ground Theory Heights  Heights Chart Max Ideals disjoint iff 260247d60a12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L78-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMaxIdeals
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_disjoint_iff_260247d60a12 {I : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F}
    {p : Ideal (MvPolynomial (Fin e × Fin n) F)} [p.IsPrime] (P : Ideal (ChartInc I t e)) :
    Disjoint (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl : Set (ChartInc I t e)) (P : Set _) ↔
      P.comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) ≤ p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMaxIdeals».«disjoint_iff» := P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_disjoint_iff_260247d60a12
