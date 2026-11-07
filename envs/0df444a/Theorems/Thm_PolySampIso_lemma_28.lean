-- Prove2me | Theorems.Thm_PolySampIso_lemma_28
-- name    : PolySampIso.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:39.181801+00:00
-- url     : https://prove2.me/theorems/6133dbe4-30d4-4e5a-bffd-5239cc563006
-- title:
--   Lemma 28, p.39 — χ²(π_t∥π) ≤ 3 for 0 < t ≤ 1/m
-- statement:
--   Let $X$ be a nonempty bounded polytope with $m$ constraints and $0<t\le1/m$. Then
--
--   $$\chi^2(\pi_t\|\pi)\le3.$$
--
--   This is the last warm start of Algorithm 5: the final cooled measure of Phase 3 is $3$-warm for the uniform measure, which the oracle $O_0$ of Phase 4 samples.
--
--   Differences from the source:
--   - encoding: χ²(πt∥π) ≤ 3 → χ² in [0, ∞]; reason: the χ² of Definitions
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 28, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_LogBarrier

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Lemma 28** (χ² warmness of `π_t` for `π` at small `t`).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 28, p.39 (PDF p.41):

"Lemma 28. Let 0 < t ≤ 1/m. Following the notation (43), we have χ2(πt∥π) ≤ 3."

**Formalization Note.** `π_t = cooled A b t` (43), `π = uniform A b`; `χ²` is in `ℝ≥0∞`. The
standing assumption of §2.3 is kept. -/
theorem lemma_28 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hX : StandingAssumption A b) (hn : 0 < n) (t : ℝ) (ht : 0 < t) (htm : t ≤ 1 / (m : ℝ)) :
    chiSq (cooled A b t) (uniform A b) ≤ 3 := by sorry

end PolySampIso
