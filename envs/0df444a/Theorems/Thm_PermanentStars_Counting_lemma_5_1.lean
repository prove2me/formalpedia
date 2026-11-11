-- Prove2me | Theorems.Thm_PermanentStars_Counting_lemma_5_1
-- name    : PermanentStars.Counting.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:42.273443+00:00
-- url     : https://prove2.me/theorems/a6dee364-17ef-4047-b908-32bc2146cc52
-- title:
--   Lemma 5.1 — Fixed parameters with exponential saving and coverage
-- statement:
--   There are a nonempty finite set $R$ of positive integer cutoffs and rational parameters $\alpha_r,c_r$ such that, for every $r\in R$,
--   $$0<\alpha_r<\tfrac12,\quad1<c_r<2,\quad c_r(c_r-1)^{r-1}\ge1,\quad E(\alpha_r,c_r)<1,$$
--   where $E(\alpha,c)=\log_2c+H(\alpha)-\alpha\log_2(c-1)$ and $H$ is binary entropy. The same fixed parameters give an admissible cutoff to every partition of $[n]$ for every $n\ge0$.
--
--   This is simultaneous coverage and an exponential saving; the parameters precede all input sizes.
--
--   Differences from the source:
--   - encoding: strictly increasing indexed cutoff list → nonempty finite set of positive cutoffs with parameters indexed by their values; reason: the natural order uniquely gives the source list, and unused function values do not enter any assertion
--   - encoding: binary entropy and logarithms to base two → Real.binEntropy divided by Real.log 2 and corresponding logarithm quotients; reason: the functions agree on every source parameter, including the continuous entropy endpoint convention
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Lemma 5.1, PDF/printed p.10

import Definitions.Def_PermanentStars_Counting_Partitions

namespace PermanentStars.Counting

/-- Lemma 5.1, p.10. One fixed finite rational parameter choice works for every n. -/
theorem lemma_5_1 :
    ∃ (P : Cutoffs) (c : ℕ → ℚ), P.Valid ∧
      (∀ r ∈ P.R, 0 < P.alpha r ∧ P.alpha r < 1 / 2 ∧
        1 < c r ∧ c r < 2 ∧ 1 ≤ c r * (c r - 1) ^ (r - 1) ∧
        exponent (P.alpha r : ℝ) (c r : ℝ) < 1) ∧
      ∀ n : ℕ, Covers P n := by sorry

end PermanentStars.Counting
