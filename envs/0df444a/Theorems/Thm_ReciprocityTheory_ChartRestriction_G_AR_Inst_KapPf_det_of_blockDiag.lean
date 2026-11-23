-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_det_of_blockDiag
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.det_of_blockDiag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:35.674704+00:00
-- url     : https://prove2.me/theorems/be17da78-a1bc-45f2-ba84-5385b301279b
-- title:
--   Kap Pf: det of block Diag
-- statement:
--   The Kap Pf construction uses the det of block Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DetOfBlockDiag.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/DetOfBlockDiag.lean#L14-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.det_of_blockDiag {m α : Type} [Fintype m] [DecidableEq m] [LinearOrder α] (M : Matrix m m ℂ)
    (bk : m → α) (hM : M.BlockTriangular bk) (dg : m → ℂ)
    (hd : ∀ i j, bk i = bk j → M i j = if i = j then dg i else 0) : M.det = ∏ i, dg i := by sorry
