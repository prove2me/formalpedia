-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm2020_finite_sampling_bound
-- name    : QuantumMaxCutEnergy.agm2020_finite_sampling_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T00:57:27.60563+00:00
-- url     : https://prove2.me/theorems/2f9fdecb-a1dd-45d2-bb09-2b7ddf350050
-- title:
--   Finite sampling bound for matching energy
-- statement:
--   Let $X$ be a real-valued random variable on a finite nonempty uniform sample space. If $0\le m\le W$, every sample satisfies $0\le X\le2W$, and $\mathbb E[X]\ge3m/2+W/2$, then
--
--   $$\Pr[X\ge3m/2+0.49W]\ge1/151.$$
--
--   This verifies the sampling estimate printed between Eqs. (29) and (30), including the zero-weight case.
-- source:
--   Anshu, Gosset, and Morenz, TQC 2020, p. 7:10, sampling-probability display between Eqs. (29) and (30), in the proof of Theorem 3. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . The formalization specializes the displayed bound 0.01/1.51 = 1/151 to a finite nonempty uniform sample space.

import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.agm2020_finite_sampling_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (W m : ℝ)
    (hW : 0 ≤ W) (hm : 0 ≤ m) (hmW : m ≤ W)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 2 * W)
    (hmean : 3 * m / 2 + W / 2 ≤ (∑ ω, X ω) / (Fintype.card Ω : ℝ)) :
    (1 / 151 : ℝ) ≤
      ((Finset.univ.filter (fun ω => 3 * m / 2 + 0.49 * W ≤ X ω)).card : ℝ) /
        (Fintype.card Ω : ℝ) := by sorry
