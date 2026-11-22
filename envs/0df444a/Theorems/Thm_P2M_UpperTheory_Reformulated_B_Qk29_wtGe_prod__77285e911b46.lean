-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46
-- name    : P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:21.997004+00:00
-- url     : https://prove2.me/theorems/354e7f47-89d0-4983-95ec-dd1a4bb47c14
-- title:
--   P2 M Upper Theory Reformulated B Qk29 wt Ge prod  77285e911b46: P2 M Upper Theory Reformulated B Qk29 wt Ge prod  77285e911b46
-- statement:
--   The P2 M Upper Theory Reformulated B Qk29 wt Ge prod  77285e911b46 construction uses the P2 M Upper Theory Reformulated B Qk29 wt Ge prod  77285e911b46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/WtGeProd.lean#L56-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/WtGeProd.lean#L56-L68

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} [IsUltrametricDist K] {pi : ℝ},
      (0 : ℝ) < pi →
        ∀ {r : ι → ℝ} {α : Type w} (s : Finset α) (wt : α → ℝ) (F : α → MvPowerSeries ι K),
          (∀ i ∈ s, UpperTheory.Reformulated.B.Qk29.WtGe pi r (wt i) (F i)) → UpperTheory.Reformulated.B.Qk29.WtGe pi r (∑ i ∈ s, wt i) (∏ i ∈ s, F i) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qk29».«wtGe_prod» := P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46
