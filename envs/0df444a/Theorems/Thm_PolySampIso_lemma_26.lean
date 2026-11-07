-- Prove2me | Theorems.Thm_PolySampIso_lemma_26
-- name    : PolySampIso.lemma_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:10.280676+00:00
-- url     : https://prove2.me/theorems/18ac6008-e4ad-4066-ad6d-f3abfd91b48d
-- title:
--   Lemma 26, p.38 — χ²(π_t∥π_{t′}) ≤ e − 1 across one Phase 2 step
-- statement:
--   Let $X$ be a nonempty bounded polytope in $\mathbb R^n$, $t>0$ and $t'=t(1+1/\sqrt n)^{-1}$. Then
--
--   $$\chi^2(\pi_t\|\pi_{t'})\le e-1.$$
--
--   One Phase 2 update of the inverse temperature changes the cooled measure by a bounded $\chi^2$ amount, so each stage of Phase 2 warm-starts the next.
--
--   Differences from the source:
--   - encoding: χ²(πt∥πt′) ≤ e − 1 → χ² in [0, ∞], bound ENNReal.ofReal(e − 1); reason: the χ² of Definitions
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 26, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_LogBarrier

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Lemma 26** (χ² warmness across one Phase 2 step of the cooling schedule).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 26, p.38 (PDF p.40):

"Lemma 26. Let t > 0 and t′ := t · (1 + 1/√n)−1. Following the notation (43), we have χ2(πt∥πt′) ≤ e − 1."

**Formalization Note.** `π_t = cooled A b t` (43); `t′ := t · (1 + 1/√n)^{−1}`; `χ²` is in `ℝ≥0∞` and
`e − 1` is `ENNReal.ofReal (exp 1 − 1)`. The standing assumption of §2.3 is kept. -/
theorem lemma_26 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hX : StandingAssumption A b) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    chiSq (cooled A b t) (cooled A b (t * (1 + 1 / Real.sqrt n)⁻¹)) ≤ ENNReal.ofReal (Real.exp 1 - 1) := by sorry

end PolySampIso
