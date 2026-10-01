-- Prove2me | Theorems.Thm_ShorAlgorithms_Reduction_nontrivial_factor_of_even_of_ne_neg_one
-- name    : ShorAlgorithms.Reduction.nontrivial_factor_of_even_of_ne_neg_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T08:27:31.960214+00:00
-- url     : https://prove2.me/theorems/d7e735cd-8880-4af7-a821-e4118ad3fcd9
-- title:
--   §5, p. 1498 — r even and x^{r/2} ≢ −1 (mod n) give a nontrivial factor gcd(x^{r/2} − 1, n)
-- statement:
--   Let $n > 1$ and let $x$ be a unit modulo $n$ with multiplicative order $r$. Since
--
--   $$
--   (x^{r/2} - 1)(x^{r/2} + 1) = x^r - 1 \equiv 0 \pmod n,
--   $$
--
--   the numbers $\gcd(x^{r/2} \pm 1, n)$ are factors of $n$. The theorem states that if $r$ is even and $x^{r/2} \not\equiv -1 \pmod n$, then
--
--   $$
--   1 < \gcd\bigl(x^{r/2} - 1,\ n\bigr) < n .
--   $$
--
--   So the reduction can fail only when $r$ is odd or $x^{r/2} \equiv -1 \pmod n$. This is the criterion on which the probability estimate of the mission rests.
--
--   **Formalization Note** Shor states the procedure for odd $n$; oddness is not needed for this step and is not assumed. The gcd is `factorCandidate n u` from the definition `successEvent`, computed from the least nonnegative residue of $x^{r/2}$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1498, §5, "Since (x^{r/2} − 1)(x^{r/2} + 1) = x^r − 1 ≡ 0 (mod n), … This procedure fails only if r is odd, … or if x^{r/2} ≡ −1 (mod n)"

import Mathlib
import Definitions.Def_ShorAlgorithms_Reduction_successEvent

namespace ShorAlgorithms.Reduction

/-- Shor (1997), §5, p. 1498: if the order `r` of `x` is even and `x^{r/2} ≢ -1 (mod n)`,
then `gcd(x^{r/2} - 1, n)` is a nontrivial factor of `n`. -/
theorem nontrivial_factor_of_even_of_ne_neg_one (n : ℕ) (hn : 1 < n) (u : (ZMod n)ˣ)
    (heven : Even (orderOf u)) (hne : (u : ZMod n) ^ (orderOf u / 2) ≠ -1) :
    1 < factorCandidate n u ∧ factorCandidate n u < n := by sorry

end ShorAlgorithms.Reduction
