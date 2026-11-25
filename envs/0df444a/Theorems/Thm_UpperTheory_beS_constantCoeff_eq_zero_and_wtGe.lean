-- Prove2me | Theorems.Thm_UpperTheory_beS_constantCoeff_eq_zero_and_wtGe
-- name    : UpperTheory.beS_constantCoeff_eq_zero_and_wtGe
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:13:39.779217+00:00
-- url     : https://prove2.me/theorems/f5cf894e-0e29-4d04-a446-c81139785ff5
-- title:
--   Upper Theory: be S constant Coeff eq zero and wt Ge
-- statement:
--   The Upper Theory construction uses the be S constant Coeff eq zero and wt Ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/BeSConstantCoeffEqZeroAndWtGe.lean#L39-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/BeSConstantCoeffEqZeroAndWtGe.lean#L39-L102

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ColDefs
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_BeSConstantCoeffEqZeroAndWtGe
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

theorem UpperTheory.beS_constantCoeff_eq_zero_and_wtGe :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l i : ℕ) [NeZero i], l.Prime → Odd l → ‖(l : K)‖ < 1 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ (2 * i) - 1) →
    ∀ (Lt β : Type) [Fintype Lt] [Fintype β] [DecidableEq Lt] [DecidableEq β] (pos : Lt → ℕ → Lt), IsPos i pos →
    ∀ sig : Lt → ℝ, IsRadii l pos sig → ∀ (R : Finset Lt) (sg : Lt → K) (be : Lt → MvPowerSeries (ZMod (2 * i)) K),
    (∀ r ∈ R, sg r = 1 ∨ sg r = -1) → (∀ r ∈ R, BHyp l (2 * i) K0 ζ (be r)) →
    MvPowerSeries.constantCoeff (beS (β := β) i pos R sg be) = 0 ∧
      WtGe ‖(l : K)‖ (fun v : Lt × β => rho l + sig v.1) (1 / ((l : ℝ) - 1)) (beS (β := β) i pos R sg be) := by sorry
