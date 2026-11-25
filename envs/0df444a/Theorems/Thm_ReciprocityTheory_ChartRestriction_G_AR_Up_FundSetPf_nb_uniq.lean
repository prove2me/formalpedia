-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_nb_uniq
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.nb_uniq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:20.831946+00:00
-- url     : https://prove2.me/theorems/b92f2086-e587-5e8e-a77c-2635064b49ed
-- title:
--   Fund Set Pf: nb uniq
-- statement:
--   The Fund Set Pf construction uses the nb uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FundSetPf.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FundSetPf.lean#L36-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.nb_uniq {N N' B B' : Matrix (Fin r) (Fin r) ℂ} (hN : ∀ a c : Fin r, a < c → N a c = 0)
    (hN1 : ∀ a, N a a = 1) (hN' : ∀ a c : Fin r, a < c → N' a c = 0) (hN'1 : ∀ a, N' a a = 1)
    (hB : ∀ a c : Fin r, c < a → B a c = 0) (hB' : ∀ a c : Fin r, c < a → B' a c = 0) (hBd : B.det ≠ 0)
    (h : N * B = N' * B') : N = N' := by sorry
