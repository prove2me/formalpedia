-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_HD_map_sq
-- name    : ReciprocityTheory.ChartRestriction.L1.HD.map_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:20.195162+00:00
-- url     : https://prove2.me/theorems/ad465f47-25fa-583a-bd96-ccea68fcbc09
-- title:
--   HD: map sq
-- statement:
--   The HD construction uses the map sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonF.lean#L47-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonF.lean#L47-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem ReciprocityTheory.ChartRestriction.L1.HD.map_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) :
    HD σ (PowerSeries.map ((σ.comp σ) ^ i) lam) (MvPowerSeries.map ((σ.comp σ) ^ i) Φ)
      (PowerSeries.map ((σ.comp σ) ^ i) A) a := by sorry
