-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P50_idealComb_rephasing
-- name    : QAlgorithms.Papers.Independent.Extend50.P50.idealComb_rephasing
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T21:27:38.181399+00:00
-- url     : https://prove2.me/theorems/cf699225-d93e-4222-bb16-2d9d41073448
-- title:
--   Ideal integer-spaced atomic comb: exact single-excitation recurrence
-- statement:
--   Consider $N\ge1$ distinguishable two-level atoms. Write $|j\rangle=|b_1\cdots a_j\cdots b_N\rangle$ for the configuration with only atom $j$ excited. Let $\Delta>0$ be a common angular-frequency spacing and $r_j\in\mathbb Z$ the tooth labels, so that $\delta_j=r_j\Delta$. Let $a_j\in\mathbb C$ satisfy $\sum_{j=1}^N|a_j|^2=1$; the coefficients include the fixed carrier phase $e^{ikz_j}$ of Eq.(5). Define the ideal evolving vector $\Psi(t)=\sum_{j=1}^N a_j e^{-i\delta_jt}|j\rangle$. For every positive integer $m$,
--
--   $$
--   \Psi\!\left(m\frac{2\pi}{\Delta}\right)=\Psi(0).
--   $$
--
--   This gives exact phase recurrence in the ideal tooth-center model. It does not turn finite-width teeth into an exact retrieval channel or supply an efficiency, fidelity, capacity, or controllable-readout theorem.
-- source:
--   Optical quantum memory, arXiv:1002.4659v3, PDF p. 8, II.D.3; Eq.(5) on p.6; Fig.5 on p.10

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P50

namespace QAlgorithms.Papers.Independent.Extend50.P50

/-- PDF p.8, II.D.3, with Eq.(5) on p.6 and Fig.5 on p.10: a normalized
single-excitation wave in an ideal integer-spaced comb returns exactly to its
initial vector at every positive integer multiple of `2π / spacing`.
Normalization suppressed in Eq.(5) is restored in the coefficient hypothesis.
No retrieval efficiency, finite-width recurrence, or on-demand readout is asserted. -/
theorem idealComb_rephasing (N : ℕ) (hN : 1 ≤ N)
    (r : Fin N → ℤ) (spacing : ℝ) (hspacing : 0 < spacing)
    (a : Fin N → ℂ) (ha : ∑ j : Fin N, Complex.normSq (a j) = 1) :
    ∀ m : ℕ, 0 < m →
      detuningPhaseWave a (idealCombDetuning r spacing)
        ((m : ℝ) * (2 * Real.pi / spacing)) =
      detuningPhaseWave a (idealCombDetuning r spacing) 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P50
