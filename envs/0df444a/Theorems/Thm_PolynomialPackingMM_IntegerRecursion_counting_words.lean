-- Prove2me | Theorems.Thm_PolynomialPackingMM_IntegerRecursion_counting_words
-- name    : PolynomialPackingMM.IntegerRecursion.counting_words
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:53.029901+00:00
-- url     : https://prove2.me/theorems/b3e73f94-fe0f-4249-8283-a95106205bb4
-- title:
--   Claim 3.3 — counting words by type
-- statement:
--   Let $f,g\ge0$ and $d\ge1$ be integers with $m=f+g\ge1$. The first $d$ positions choose from $f$ tagged Full letters and $g$ tagged Mid letters; the last $d$ positions choose from $g$ tagged Full letters and $f$ tagged Mid letters. Let $M_d$ count words with exactly $d$ letters of each type. Then
--
--   $$M_d\ge\frac{m^{2d}}{d+1}.$$
--
--   This is the lower bound for retaining balanced targets. **Formalization Note** It is an exact rational inequality between the actual finite-word cardinality and the fraction. Both $f=0$ and $g=0$ are allowed; the bound is not replaced by a floor.
--
--   Differences from the source:
--   - encoding: nonnegative f and g, positive d, and distinctly labelled letters → natural f and g, positive natural d, and finite tagged alphabets; reason: every source word and boundary case has exactly one encoded word
--   - encoding: the exact fraction m^(2d)/(d+1) → a rational comparison with the actual word cardinality; reason: the denominator is positive and no floor weakens the bound
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 14 (PDF 15), Claim 3.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_PackingOperations

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

theorem counting_words :
  ∀ (f g : ℕ) (d : ℕ+), 1 ≤ f + g →
  ((f + g : ℕ) : ℚ) ^ (2 * (d : ℕ)) / ((d : ℕ) + 1 : ℚ) ≤
    (balancedWordCount f g d : ℚ) := by sorry

end PolynomialPackingMM.IntegerRecursion
