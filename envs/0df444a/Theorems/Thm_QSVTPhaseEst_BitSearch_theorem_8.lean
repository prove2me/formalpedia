-- Prove2me | Theorems.Thm_QSVTPhaseEst_BitSearch_theorem_8
-- name    : QSVTPhaseEst.BitSearch.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:41.145731+00:00
-- url     : https://prove2.me/theorems/e47b23f4-e50a-42d8-972f-adac0b5fe0bc
-- title:
--   Theorem 8, p. 17 — if Δ < 2(cos(3π/16) − 1/√2), the Δ-region is met only at iteration n − 1 and every run outputs θ with |θ − φ| < 2^{−n}
-- statement:
--   Let $U$ be a unitary with eigenvalue $e^{2\pi i\varphi}$, $0 \le \varphi < 1$, and run phase estimation by QSVT (Algorithm 3) for $n \ge 1$ iterations with a polynomial approximation of the sign function that may err only on the Δ-region $\bigl[\tfrac1{\sqrt2} - \tfrac\Delta2, \tfrac1{\sqrt2} + \tfrac\Delta2\bigr]$. If
--   $$0 \le \Delta < 2\Bigl(\cos\frac{3\pi}{16} - \frac1{\sqrt2}\Bigr) \approx 0.25,$$
--   then for every run in which each bit with singular value outside the Δ-region is measured correctly:
--
--   1. the singular value $\sigma^j$ can lie in the Δ-region only at the iteration $j = n - 1$ (and not at the additional $j = 0$ iteration), so an error due to $\Delta$ can only occur at iteration $n - 1$;
--   2. the output satisfies
--   $$|\theta - \varphi| < \frac1{2^n}.$$
--
--   This is the robustness guarantee of phase estimation by QSVT: replacing the discontinuous sign function by a polynomial that is inaccurate on a band of width $\Delta$ costs at most one bit of accuracy, and only at the first iteration.
--
--   **Formalization Note** "An error due to $\Delta$" is a bit measured inside the Δ-region against the exact sign function, and "assuming no errors are made at later iterations" is the outcome rule outside it; both are the run predicate. The bound in item 2 is stated for every run: runs with an error at iteration $n - 1$ are the case printed in Theorem 8, runs without one are covered by Theorems 6 and 7 ($\le 2^{-n-1}$), and Algorithm 3's Output claims $|\theta - \varphi| \le 2^{-n}$ unconditionally. Item 1 extends "only possible at the $j = n - 1$ iteration" to the additional $j = 0$ iteration. That iteration is encoded as in Appendix B 1 b, p. 29 (singular value $|\cos(\pi(\varphi - \theta_0)/2)|$, units digit of the output). The probabilistic $\epsilon$-errors of (71)–(72) are not modelled.
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, p. 17, Theorem 8 (70) (restated p. 30, (B13)); Algorithm 3, Output, p. 17; proof pp. 30–31

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace QSVTPhaseEst.BitSearch

theorem theorem_8 (Δ φ : ℝ) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ < 2 * (Real.cos (3 * Real.pi / 16) - 1 / Real.sqrt 2))
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (n : ℕ) (hn : 1 ≤ n)
    (b : ℕ → Bool) (b₀ : Bool) (hrun : IsRun Δ φ n b b₀) :
    ((∀ j < n, j ≠ n - 1 → ¬ InDeltaRegion Δ (sigma φ j (thetaAfter n b (j + 1) / 2))) ∧
      ¬ InDeltaRegion Δ (extraSigma φ n b)) ∧
    |output n b b₀ - φ| < ((2 : ℝ) ^ n)⁻¹ := by sorry

end QSVTPhaseEst.BitSearch
