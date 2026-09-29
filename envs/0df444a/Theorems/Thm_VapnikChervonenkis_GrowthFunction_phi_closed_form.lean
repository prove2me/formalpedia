-- Prove2me | Theorems.Thm_VapnikChervonenkis_GrowthFunction_phi_closed_form
-- name    : VapnikChervonenkis.GrowthFunction.phi_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:34:56.495536+00:00
-- url     : https://prove2.me/theorems/ccd623c3-bd2a-4d7c-9529-98804fefbf46
-- title:
--   Closed form of Φ(n, r)
-- statement:
--   Let $\Phi(n, r)$ be defined by the recurrence (1): $\Phi(n, r) = \Phi(n, r-1) + \Phi(n-1, r-1)$, $\Phi(0, r) = 1$, $\Phi(n, 0) = 1$. Then for all natural numbers $n$ and $r$,
--
--   $$
--   \Phi(n, r) = \begin{cases} \displaystyle\sum_{k=0}^{n} \binom{r}{k} & \text{if } r > n, \\[1ex] 2^r & \text{if } r \le n. \end{cases}
--   $$
--
--   The closed form identifies $\Phi(n, r)$ as the partial binomial sum of the Sauer–Shelah lemma. The polynomial bound $\Phi(n, r) \le r^n + 1$ follows from it.
--
--   **Formalization Note.** The printed display has $\binom{r}{n}$ as the summand, a misprint for $\binom{r}{k}$: with $\binom{r}{n}$ the formula gives $\Phi(1, 2) = 4$, whereas the recurrence gives $\Phi(1, 2) = 3$. The statement uses $\binom{r}{k}$. The sum runs over $k = 0, \dots, n$ (`Finset.range (n + 1)`), and the case split is written as printed although both branches equal $\sum_{k=0}^{n} \binom{r}{k}$.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 266, display after Eq. (1) (printed summand (r over n) corrected to (r over k))

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi

namespace VapnikChervonenkis.GrowthFunction

/-- Vapnik and Chervonenkis (1971), p. 266, display after (1): `Φ(n, r) = Σ_{k=0}^{n} (r choose k)`
if `r > n`, and `Φ(n, r) = 2^r` if `r ≤ n`. (The printed summand reads `(r choose n)`, a misprint
for `(r choose k)`: with `(r choose n)` the formula already fails at `Φ(1, 2) = 3`.) -/
theorem phi_closed_form (n r : ℕ) :
    Shared.Phi n r = if n < r then ∑ k ∈ Finset.range (n + 1), r.choose k else 2 ^ r := by sorry

end VapnikChervonenkis.GrowthFunction
