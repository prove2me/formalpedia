-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_Mq_cpt__b80e492a86ff
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_Mq_cpt__b80e492a86ff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:21.562335+00:00
-- url     : https://prove2.me/theorems/b65b2543-98ce-578d-a36f-590cefc030cd
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf Mq cpt  b80e492a86ff: P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf Mq cpt  b80e492a86ff
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf Mq cpt  b80e492a86ff construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf Mq cpt  b80e492a86ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfH.lean#L108-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfH.lean#L108-L109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_Mq_cpt__b80e492a86ff (X : Data E r) (x0 x : Frame X.Ψ r) (w : V (nd X)) (τ : X.Ψ) :
    Mq X x0 (cpt X x w) τ = Mq X x0 x τ * Nw X w τ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«PoinPf».«Mq_cpt'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_Mq_cpt__b80e492a86ff
