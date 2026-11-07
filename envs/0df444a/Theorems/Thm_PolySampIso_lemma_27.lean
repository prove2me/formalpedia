-- Prove2me | Theorems.Thm_PolySampIso_lemma_27
-- name    : PolySampIso.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:24.635604+00:00
-- url     : https://prove2.me/theorems/a5ba309b-9398-4f53-96c7-0c05c55455de
-- title:
--   Lemma 27, p.39 — χ²(π_t∥π_{t′}) ≤ e − 1 across one Phase 3 step
-- statement:
--   Let $X$ be a nonempty bounded polytope with $m$ constraints, $t>0$ and $t'=t(1+1/\sqrt{mt})^{-1}$. Then
--
--   $$\chi^2(\pi_t\|\pi_{t'})\le e-1.$$
--
--   This is the warmness of consecutive stages in Phase 3, whose larger steps at small $t$ use the $m$-self-concordance of $\psi$.
--
--   Differences from the source:
--   - encoding: χ²(πt∥πt′) ≤ e − 1 → χ² in [0, ∞], bound ENNReal.ofReal(e − 1); reason: the χ² of Definitions
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 27, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_LogBarrier

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Lemma 27** (χ² warmness across one Phase 3 step of the cooling schedule).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 27, p.39 (PDF p.41):

"Lemma 27. Let t > 0 and t′ := t · (1 + 1/√mt)−1. Following the notation (43), we have χ2(πt∥πt′) ≤ e − 1."

**Formalization Note.** `π_t = cooled A b t` (43); `t′ := t · (1 + 1/√(mt))^{−1}`; `χ²` is in `ℝ≥0∞` and
`e − 1` is `ENNReal.ofReal (exp 1 − 1)`. The standing assumption of §2.3 is kept. -/
theorem lemma_27 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hX : StandingAssumption A b) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    chiSq (cooled A b t) (cooled A b (t * (1 + 1 / Real.sqrt (m * t))⁻¹)) ≤ ENNReal.ofReal (Real.exp 1 - 1) := by sorry

end PolySampIso
