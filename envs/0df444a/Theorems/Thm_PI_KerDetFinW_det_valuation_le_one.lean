-- Prove2me | Theorems.Thm_PI_KerDetFinW_det_valuation_le_one
-- name    : PI.KerDetFinW.det_valuation_le_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:38.031946+00:00
-- url     : https://prove2.me/theorems/ce3b41cb-4782-5322-b2d4-4ee2cffc0f9f
-- title:
--   Ker Det Fin W: det valuation le one
-- statement:
--   The Ker Det Fin W construction uses the det valuation le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ValuationLeOneOfDenom.lean#L83-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ValuationLeOneOfDenom.lean#L83-L108

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso

theorem PI.KerDetFinW.det_valuation_le_one {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type}
    [Fintype n] {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal)
    (hg : AtP M g p) (hg' : AtP M g' p) :
    𝔭.valuation K (LinearMap.det ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
      (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))) ≤ 1 := by sorry
