-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_psgn_dmin_gt
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.psgn_dmin_gt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:07.572688+00:00
-- url     : https://prove2.me/theorems/7ba766d5-db1d-4b99-bf67-237f37ec3cbf
-- title:
--   Ex F: psgn dmin gt
-- statement:
--   The Ex F construction uses the psgn dmin gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustFStatementPfB.lean#L143-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustFStatementPfB.lean#L143-L279

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.psgn_dmin_gt {x : Frame X.Ψ r} (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (hA : (X.gramPos x τ).PosDef) (k : ℕ) (hk : X.p0 + k ≤ r) (i : Fin (r + 1))
    (hik : (i : ℕ) = X.p0 + k) : 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by sorry
