-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_fin_integral
-- name    : ReciprocityTheory.ChartRestriction.L1.fin_integral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:44:21.642082+00:00
-- url     : https://prove2.me/theorems/d7a25edc-0c7e-57a0-ab6e-128333658ffe
-- title:
--   L1: fin integral
-- statement:
--   The L1 construction uses the fin integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgFinA.lean#L115-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgFinA.lean#L115-L178

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgFinA
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

theorem ReciprocityTheory.ChartRestriction.L1.fin_integral [CompleteSpace K] (hF : FrobField K l σ) (ex lam : PowerSeries K)
    (hlam0 : constantCoeff lam = 0) (hlam1 : coeff 1 lam = 1) (hex0 : constantCoeff ex = 0)
    (hinv : ex.subst lam = X) (c ε : K) (hc : ‖c‖ = 1) (hε : ‖ε‖ = 1) (hcε : ε = c * σ (σ ε))
    (hT : IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    IntegralPS (ex.subst (C ε * ltLog K l)) := by sorry
