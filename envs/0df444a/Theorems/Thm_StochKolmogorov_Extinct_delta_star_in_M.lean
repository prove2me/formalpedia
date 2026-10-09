-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_delta_star_in_M
-- name    : StochKolmogorov.Extinct.delta_star_in_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:55.144882+00:00
-- url     : https://prove2.me/theorems/8c335bd5-9fdf-4421-a347-72271b50e7d8
-- title:
--   p. 5 — the zero Dirac law belongs to M
-- statement:
--   The zero state is absorbing for the Kolmogorov equation. Its Dirac probability law $\delta_*$ is therefore ergodic, invariant, and supported on the boundary:
--
--   $$\delta_*\in M.$$
--
--   This verifies that the family of boundary ergodic laws is nonempty under the standing model.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §1.1, p. 5, paragraph beginning “Let M be the set”

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem delta_star_in_M {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    (Measure.dirac (0 : SDEState n)) ∈ bdryErgodic P X := by sorry

end StochKolmogorov.Extinct
