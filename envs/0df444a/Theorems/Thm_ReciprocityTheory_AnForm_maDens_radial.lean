-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_maDens_radial
-- name    : ReciprocityTheory.AnForm.maDens_radial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:01.991366+00:00
-- url     : https://prove2.me/theorems/653a3dc2-63f6-403e-8ffc-52cb7622064b
-- title:
--   An Form: ma Dens radial
-- statement:
--   The An Form construction uses the ma Dens radial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L56-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L56-L69

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section

theorem ReciprocityTheory.AnForm.maDens_radial (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (h h' h'' : ℝ → ℝ) (z : Fin 1 → ℂ)
    (hφ : φ 0 =ᶠ[𝓝 z] fun y => h (‖y 0‖ ^ 2))
    (hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt h (h' t) t)
    (hd2 : HasDerivAt h' (h'' (‖z 0‖ ^ 2)) (‖z 0‖ ^ 2)) :
    maDens φ z = 2 / Real.pi * (h'' (‖z 0‖ ^ 2) * ‖z 0‖ ^ 2 + h' (‖z 0‖ ^ 2)) := by sorry
