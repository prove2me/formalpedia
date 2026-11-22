-- Prove2me | Theorems.Thm_SKHessianAscent_proposition_2_3
-- name    : SKHessianAscent.proposition_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:01:05.768281+00:00
-- url     : https://prove2.me/theorems/b9e0fdd0-4e6e-4802-90a5-c8aede742da3
-- title:
--   Proposition 2.3 — GOE operator norm concentration: $\Pr\{\|A\|_{\mathrm{op}}>3\}\le 2e^{-n/4}$
-- statement:
--   Let $A\sim\mathrm{GOE}(n)$ be a normalized GOE matrix: $A$ is symmetric, with independent entries $A_{ij}\sim N(0,1/n)$ for $i<j$ and $A_{ii}\sim N(0,2/n)$. Then
--
--   $$
--   \Pr\big\{\|A\|_{\mathrm{op}}>3\big\}\le 2e^{-n/4},
--   $$
--
--   where $\|\cdot\|_{\mathrm{op}}$ is the Euclidean operator norm.
--
--   The event $\{\|A\|_{\mathrm{op}}\le3\}$ is the basic high-probability event on which the deterministic estimates of the paper (Lemma 4.3, Corollary 6.10) are proved.
--
--   **Formalization Note** $\mathrm{GOE}(n)$ is the published `RandMatDisc.goe n`, a measure on `Fin n → Fin n → ℝ`; the statement holds for every $n\ge0$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Proposition 2.3, eq. (2.5), p. 6

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem proposition_2_3 (n : ℕ) :
    RandMatDisc.goe n {A | 3 < opNorm (Matrix.of A)} ≤
      ENNReal.ofReal (2 * Real.exp (-(n : ℝ) / 4)) := by sorry

end SKHessianAscent
