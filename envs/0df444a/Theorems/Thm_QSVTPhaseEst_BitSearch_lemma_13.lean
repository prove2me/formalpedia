-- Prove2me | Theorems.Thm_QSVTPhaseEst_BitSearch_lemma_13
-- name    : QSVTPhaseEst.BitSearch.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:38.631749+00:00
-- url     : https://prove2.me/theorems/6432906c-e124-42c2-a38e-e3a4db20fb9d
-- title:
--   Lemma 13, p. 30 — if 1/4 − arccos(1/√2 + Δ/2)/π < 1/16, σ^j can only be inside the Δ-region at iteration j = n − 1
-- statement:
--   Let $\Delta \ge 0$ satisfy (B16),
--   $$\frac14 - \frac1\pi\arccos\Bigl(\frac1{\sqrt2} + \frac\Delta2\Bigr) < \frac1{16},$$
--   let $0 \le \varphi < 1$ and $n \ge 1$, and consider any complete run of phase estimation by QSVT in which every bit whose singular value lies outside the Δ-region is measured correctly (outcome rule with width $\Delta$). Then
--
--   1. for every iteration $j < n$ with $j \ne n - 1$, the singular value $\sigma^j(\theta_{j+1}/2)$ is outside the Δ-region;
--   2. the singular value of the additional $j = 0$ iteration is outside the Δ-region.
--
--   So an approximate sign function can only err at the first iteration $j = n - 1$.
--
--   **Formalization Note** The proof's assumption "if $\sigma^j$ is outside of the Δ-region, then we can correctly determine $\theta_1$" is the outcome rule; inside the region both bits are allowed. Item 2 extends "only at iteration $j = n-1$" to the additional $j = 0$ iteration, encoded as in Appendix B 1 b (singular value $|\cos(\pi(\varphi - \theta_0)/2)|$).
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, p. 30, Lemma 13 (B16); proof pp. 30–31

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace QSVTPhaseEst.BitSearch

theorem lemma_13 (Δ φ : ℝ) (hΔ0 : 0 ≤ Δ)
    (hB16 : 1 / 4 - Real.arccos (1 / Real.sqrt 2 + Δ / 2) / Real.pi < 1 / 16)
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (n : ℕ) (hn : 1 ≤ n)
    (b : ℕ → Bool) (b₀ : Bool) (hrun : IsRun Δ φ n b b₀) :
    (∀ j < n, j ≠ n - 1 → ¬ InDeltaRegion Δ (sigma φ j (thetaAfter n b (j + 1) / 2))) ∧
      ¬ InDeltaRegion Δ (extraSigma φ n b) := by sorry

end QSVTPhaseEst.BitSearch
