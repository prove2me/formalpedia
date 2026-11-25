-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfA_maj_chart
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.maj_chart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:31:26.843107+00:00
-- url     : https://prove2.me/theorems/36e60ba5-2ec6-421e-94da-1439ee983f6f
-- title:
--   Mode Half A: maj chart
-- statement:
--   The Mode Half A construction uses the maj chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfA.lean#L56-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfA.lean#L56-L80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.maj_chart (X : Data E r) {w : Frame X.Ψ r} {τ : X.Ψ} {Y : Matrix (Fin r) (Fin r) ℂ}
    (hY : FD.gram τ.1 X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (N : Fin r → Fin r → ℂ) (hw : mat w τ = Y * Matrix.of N) (v : Fin r → ℂ) :
    X.maj w τ v = Ms X.p0 X.p0_le N (Y⁻¹ *ᵥ v) := by sorry
