-- Prove2me | Theorems.Thm_SpikedWishart_FixedDim_eq_27
-- name    : SpikedWishart.FixedDim.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:36.951327+00:00
-- url     : https://prove2.me/theorems/39fcda84-3385-4bc9-90d2-d80090e664a0
-- title:
--   (27), p. 1648 — Selberg's integral: Z_k = (2π)^{k/2} Π_{j=1}^k j!
-- statement:
--   For every integer $k \ge 1$,
--   $$Z_k = \int_{\mathbb R^k}\prod_{1\le i<j\le k}|\xi_i-\xi_j|^2\cdot\prod_{i=1}^k e^{-\frac12\xi_i^2}\,d\xi_1\cdots d\xi_k = (2\pi)^{k/2}\prod_{j=1}^k j! .$$
--
--   This is the Gaussian (Mehta) case of Selberg's integral, the normalization of the GUE eigenvalue density (26). In Proposition 1.1 it identifies the limit of the normalized constants of (304) with the normalization of $G_k$.
--
--   **Formalization Note** $Z_k$ is defined as the integral in the definitions file; this theorem is its evaluation. The power $(2\pi)^{k/2}$ is a real power.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1648, §1.2.2, (27)

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_GUE

namespace SpikedWishart.FixedDim

theorem eq_27 (k : ℕ) (hk : 1 ≤ k) :
    Z k = (2 * Real.pi) ^ ((k : ℝ) / 2) * ∏ j ∈ Finset.Icc 1 k, (j.factorial : ℝ) := by sorry

end SpikedWishart.FixedDim
