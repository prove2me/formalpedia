-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_rank3_odd_series_ratio_0954
-- name    : QuantumMaxCutEnergy.rank3_odd_series_ratio_0954
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:49:25.788004+00:00
-- url     : https://prove2.me/theorems/87c68629-f093-4e82-9c2d-f93cec5e2bb8
-- title:
--   A certified 0.954 bound from the positive odd correlation series
-- statement:
--   Let c be a nonnegative summable real sequence whose sum is one, with c₀≥8/(3π) and c₁≥4/(15π). For every real t with −1≤t<1, the ratio (1−Σₙcₙt^(2n+1))/(1−t) is at least 0.954. The theorem proves a uniform exact analytic lower bound from the stated series hypotheses. The Gaussian correlation identity and the verification that its coefficients satisfy these hypotheses are separate obligations.
-- source:
--   Briët, de Oliveira Filho and Vallentin, Theory of Computing10(4),2014,Lemma2.1, https://doi.org/10.4086/toc.2014.v010a004 ; also Gharibian and Parekh, APPROX/RANDOM2019, AppendixC Lemma10/Eq12, p31:17, https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.31 . Exact weaker scalar certificate derived from the first two positive odd-series coefficients; no Gaussian identity is assumed proved.

import Mathlib

theorem QuantumMaxCutEnergy.rank3_odd_series_ratio_0954 (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hsum : Summable c) (hunit : (∑' n, c n) = 1)
    (hc0 : 8 / (3 * Real.pi) ≤ c 0) (hc1 : 4 / (15 * Real.pi) ≤ c 1)
    (t : ℝ) (htlow : -1 ≤ t) (hthigh : t < 1) :
    (0.954 : ℝ) ≤ (1 - ∑' n, c n * t ^ (2 * n + 1)) / (1 - t) := by sorry
