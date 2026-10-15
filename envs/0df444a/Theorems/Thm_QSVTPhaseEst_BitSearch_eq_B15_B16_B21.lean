-- Prove2me | Theorems.Thm_QSVTPhaseEst_BitSearch_eq_B15_B16_B21
-- name    : QSVTPhaseEst.BitSearch.eq_B15_B16_B21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:38.343245+00:00
-- url     : https://prove2.me/theorems/1cff4f45-15de-4f1a-a665-b35659ddb414
-- title:
--   (B15), (B16) ⟺ (B21), pp. 30–31 — 1/4 − arccos(1/√2 + Δ/2)/π < 1/16 iff Δ < 2(cos(3π/16) − 1/√2), which gives (B15) for both signs
-- statement:
--   Let $\Delta \ge 0$. Then
--
--   1. condition (B16) is equivalent to the restriction (B21):
--   $$\frac14 - \frac1\pi\arccos\Bigl(\frac1{\sqrt2} + \frac\Delta2\Bigr) < \frac1{16} \iff \Delta < 2\Bigl(\cos\frac{3\pi}{16} - \frac1{\sqrt2}\Bigr);$$
--   2. under (B21), condition (B15) holds for both signs:
--   $$\Bigl|\frac1\pi\arccos\Bigl(\frac1{\sqrt2} \pm \frac\Delta2\Bigr) - \frac14\Bigr| < \frac1{16}.$$
--
--   Item 2 is the paper's remark that "the + condition is actually more stringent". Together they convert the arccos condition of Lemma 13 into the explicit threshold $\Delta < 2(\cos(3\pi/16) - 1/\sqrt2) \approx 0.25$ of Theorem 8.
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, p. 30, (B15) and (B16); p. 31, (B21)

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace QSVTPhaseEst.BitSearch

theorem eq_B15_B16_B21 (Δ : ℝ) (hΔ0 : 0 ≤ Δ) :
    (1 / 4 - Real.arccos (1 / Real.sqrt 2 + Δ / 2) / Real.pi < 1 / 16 ↔
        Δ < 2 * (Real.cos (3 * Real.pi / 16) - 1 / Real.sqrt 2)) ∧
      (Δ < 2 * (Real.cos (3 * Real.pi / 16) - 1 / Real.sqrt 2) →
        |Real.arccos (1 / Real.sqrt 2 + Δ / 2) / Real.pi - 1 / 4| < 1 / 16 ∧
        |Real.arccos (1 / Real.sqrt 2 - Δ / 2) / Real.pi - 1 / 4| < 1 / 16) := by sorry

end QSVTPhaseEst.BitSearch
