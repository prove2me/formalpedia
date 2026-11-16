-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_Supplement_lemma_4_2
-- name    : QMomentMatch.FirstBound.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:44:36.630048+00:00
-- url     : https://prove2.me/theorems/512b8488-9a5c-495a-9828-b5493415b538
-- title:
--   Lemma 4.2 — interpolating distribution $\omega$ with the same $r-1$ moments, $\omega\ge32^{-A}\delta$ and $\|\omega-\pi_b\|_1\le\delta$
-- statement:
--   Let $2\le r\le A$ be integers and let $\pi_0\ne\pi_1$ be probability distributions on $\{0\}\cup[A]=\{0,1,\dots,A\}$ with matching moments through order $r-1$:
--   $$\sum_{s=0}^A\pi_0(s)s^k=\sum_{s=0}^A\pi_1(s)s^k\qquad(k=1,\dots,r-1).$$
--   Let $\delta=\|\pi_1-\pi_0\|_1=\sum_s|\pi_1(s)-\pi_0(s)|$. Then there is a probability distribution $\omega$ on $\{0\}\cup[A]$ with the same moments of orders $1,\dots,r-1$ such that
--   $$\omega(s)\ge32^{-A}\delta\quad(s\in\{0\}\cup[A]),\qquad\|\omega-\pi_b\|_1\le\delta\quad(b=0,1).$$
--
--   In the proof of Theorem 2.6, $\omega$ is the common endpoint of two linear paths from $\pi_0$ and $\pi_1$ along which every distribution has all its masses bounded below, as Lemma 4.1 requires.
--
--   Differences from the source:
--   - encoding: distributions on {0} ∪ [A] → probability vectors Fin (A + 1) → ℝ (base IsProbVec, moment); reason: base conventions
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 4.2, p. 24 (proof p. 33)

import Mathlib
import Definitions.Def_QMomentMatch_FirstBound_Basic

namespace QMomentMatch.FirstBound.Supplement

open QMomentMatch.FirstBound

/-- Lemma 4.2, p. 24 (proof p. 33), with `δ = ‖π_1 − π_0‖₁ = ∑_s |π_1(s) − π_0(s)|`. -/
theorem lemma_4_2 (A r : ℕ) (hr : 2 ≤ r) (hrA : r ≤ A) (π₀ π₁ : Fin (A + 1) → ℝ)
    (h₀ : IsProbVec π₀) (h₁ : IsProbVec π₁) (hne : π₀ ≠ π₁)
    (hmom : ∀ k : ℕ, 1 ≤ k → k ≤ r - 1 → moment π₀ k = moment π₁ k) :
    ∃ ω : Fin (A + 1) → ℝ, IsProbVec ω ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ r - 1 → moment ω k = moment π₀ k) ∧
      (∀ s, (∑ t, |π₁ t - π₀ t|) / (32 : ℝ) ^ A ≤ ω s) ∧
      ∑ t, |ω t - π₀ t| ≤ ∑ t, |π₁ t - π₀ t| ∧
      ∑ t, |ω t - π₁ t| ≤ ∑ t, |π₁ t - π₀ t| := by sorry

end QMomentMatch.FirstBound.Supplement
