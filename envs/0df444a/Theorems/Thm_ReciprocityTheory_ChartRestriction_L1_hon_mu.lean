-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hon_mu
-- name    : ReciprocityTheory.ChartRestriction.L1.hon_mu
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:45:22.655544+00:00
-- url     : https://prove2.me/theorems/62c065e6-7a82-4632-a67f-0a2e4ae4bc16
-- title:
--   L1: hon mu
-- statement:
--   The L1 construction uses the hon mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonF.lean#L78-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonF.lean#L78-L151

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

theorem ReciprocityTheory.ChartRestriction.L1.hon_mu (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e hh : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hh1 : HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh)
    (hh2 : DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a (lam.subst hh) ∧
      DivBy (l : K) (C (l : K) * lam - PowerSeries.subst ((X : PowerSeries K) ^ (l ^ 2)) (lam.subst hh : PowerSeries K)) ∧
      coeff 1 (lam.subst hh) = coeff 1 hh := by sorry
