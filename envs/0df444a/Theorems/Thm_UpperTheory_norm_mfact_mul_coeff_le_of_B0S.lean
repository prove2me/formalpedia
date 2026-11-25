-- Prove2me | Theorems.Thm_UpperTheory_norm_mfact_mul_coeff_le_of_B0S
-- name    : UpperTheory.norm_mfact_mul_coeff_le_of_B0S
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:55.579798+00:00
-- url     : https://prove2.me/theorems/6960541b-b690-46f5-9237-0ba937c5e6b6
-- title:
--   Upper Theory: norm mfact mul coeff le of B0 S
-- statement:
--   The Upper Theory construction uses the norm mfact mul coeff le of B0 S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/NormMfactMulCoeffLeOfB0S.lean#L69-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/NormMfactMulCoeffLeOfB0S.lean#L69-L137

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ColDefs
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_BeSConstantCoeffEqZeroAndWtGe
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_NormMfactMulCoeffLeOfB0S
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds UpperTheory.G2

theorem UpperTheory.norm_mfact_mul_coeff_le_of_B0S :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l i : ℕ) [NeZero i], l.Prime → Odd l → ‖(l : K)‖ < 1 →
    ∀ (Lt β : Type) [Fintype Lt] [Fintype β] [DecidableEq Lt] [DecidableEq β] (pos : Lt → ℕ → Lt), IsPos i pos →
    ∀ Th : MvPowerSeries (Lt × β) K, HasThetaProductForm l i pos Th → ∀ sig : Lt → ℝ, IsRadii l pos sig →
    ∀ (κ : Lt × β →₀ ℕ) (A : ℝ), 1 ≤ A → (∀ v, (κ v : ℝ) ≤ A) →
    ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th‖ ≤
      ‖(l : K)‖ ^ ((∑ v, (κ v : ℝ) * (gam l - sig v.1)) - (Fintype.card (Lt × β) : ℝ) * (Real.logb l A + 1)) := by sorry
