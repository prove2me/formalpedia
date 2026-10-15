-- Prove2me | Theorems.Thm_QSVTPhaseEst_BitSearch_eq_B17_B20
-- name    : QSVTPhaseEst.BitSearch.eq_B17_B20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:32.359761+00:00
-- url     : https://prove2.me/theorems/b4162e7a-5dab-4b8c-ae1f-bdf718708457
-- title:
--   (B17)–(B20), pp. 30–31 — whatever bit is measured at iteration n − 1, σ^{n−2} is outside the Δ-region
-- statement:
--   Let $0 \le \Delta < 2(\cos(3\pi/16) - 1/\sqrt2)$, $0 \le \varphi < 1$ and $n \ge 2$, and consider any run of the loop of phase estimation by QSVT with the outcome rule of width $\Delta$. Then at iteration $j = n - 2$ the singular value
--   $$\sigma^{n-2}\bigl(\theta_{n-1}/2\bigr)$$
--   is outside the Δ-region $\bigl[\tfrac1{\sqrt2} - \tfrac\Delta2, \tfrac1{\sqrt2} + \tfrac\Delta2\bigr]$.
--
--   This holds whether the bit measured at iteration $n - 1$ was correct ((B17), (B18)) or was an error made inside the Δ-region ((B19), (B20)): the procedure recovers from an error at its first iteration. It is the base step of Lemma 13.
--
--   **Formalization Note** The run is any bit sequence satisfying the outcome rule with width $\Delta$; at iteration $n - 1$ either bit may be measured when $\sigma^{n-1}$ is in the Δ-region.
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, pp. 30–31, proof of Lemma 13, (B17)–(B20)

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace QSVTPhaseEst.BitSearch

theorem eq_B17_B20 (Δ φ : ℝ) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ < 2 * (Real.cos (3 * Real.pi / 16) - 1 / Real.sqrt 2))
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (n : ℕ) (hn : 2 ≤ n)
    (b : ℕ → Bool) (hrun : IsLoopRun Δ φ n b) :
    ¬ InDeltaRegion Δ (sigma φ (n - 2) (thetaAfter n b (n - 1) / 2)) := by sorry

end QSVTPhaseEst.BitSearch
