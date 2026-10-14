-- Prove2me | Theorems.Thm_RiskExposure_RingComplete_lemma_IA_ii_hockey_stick
-- name    : RiskExposure.RingComplete.lemma_IA_ii_hockey_stick
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:17.640766+00:00
-- url     : https://prove2.me/theorems/9e60ae1e-e837-4d9f-b1e6-26199548e6b6
-- title:
--   Lemma I.A (ii), Internet Appendix p. 27 — Σ_{l=r}^{n} C(l, r)(n − l) = C(n+1, r+1)(n − r)/(r + 2)
-- statement:
--   For natural numbers $r<n$,
--   $$\sum_{l=r}^{n}\binom{l}{r}(n-l)=\binom{n+1}{r+1}\,\frac{n-r}{r+2}.$$
--
--   This is the second, weighted half of the paper's Hockey-stick Lemma I.A; the first half is the classical identity $\sum_{l=r}^n\binom lr=\binom{n+1}{r+1}$. In the proof of Proposition 4 it evaluates the mean number of failed upstream neighbours in the ring, which is what turns the ring's received payment into the complete network's.
--
--   **Formalization Note.** The sum ranges over `Finset.Icc r n` and the identity is stated in $\mathbb R$, so $n-l$, $n-r$ and the division by $r+2$ are real operations. Part (i) of Lemma I.A is not restated: it is the published, proved theorem `FamousTheorems.hockey_stick_identity` (Mathlib's `Nat.sum_Icc_choose`; also the second conjunct of `ProofsInTheBook.Chapter32.chapter32`).
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 27, Lemma I.A, part (ii)

import Mathlib

namespace RiskExposure.RingComplete

theorem lemma_IA_ii_hockey_stick (n r : ℕ) (h : r < n) :
    ∑ l ∈ Finset.Icc r n, (l.choose r : ℝ) * ((n : ℝ) - l) =
      ((n + 1).choose (r + 1) : ℝ) * (((n : ℝ) - r) / ((r : ℝ) + 2)) := by sorry

end RiskExposure.RingComplete
