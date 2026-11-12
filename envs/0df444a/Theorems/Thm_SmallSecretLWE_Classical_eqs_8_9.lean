-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_eqs_8_9
-- name    : SmallSecretLWE.Classical.eqs_8_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:28:01.449867+00:00
-- url     : https://prove2.me/theorems/f7131a21-f165-468a-b2ce-7c9ace342ea6
-- title:
--   §3.4.2, Eqs. (8) and (9) — lower bounds on $\theta^{(n,l,k)}$, the Kikuchi edges per row
-- statement:
--   Let $n,l,k$ be natural numbers, $q$ a positive integer and $\theta^{(n,l,k)}$ the right-hand side of Eq. (7). If $\lceil k/2\rceil\le l\le n-\lfloor k/2\rfloor$ then
--   $$\theta^{(n,l,k)}\ \ge\ \frac{2^{k-1}}{k+1}\binom{n-k}{l-\lceil k/2\rceil}(q-1)^{l-\lfloor k/2\rfloor}, \tag{8}$$
--   and if $k\le l\le n$ then
--   $$\theta^{(n,l,k)}\ \ge\ 2^{1-k}\binom{n-k}{l-k}(q-1)^{l}. \tag{9}$$
--   These two bounds give the two items of Corollary 4.8 and Theorem 5.1. As printed they carry no lower bound on $q$.
--
--   Differences from the source:
--   - encoding: $q$ the modulus of $\mathbb Z_q$, $n,l,k$ unrestricted in §3.4.2 → hypothesis $0<q$, `n l k : ℕ` arbitrary; reason: a modulus is a positive integer; nothing else is restricted, so no instance of the source is excluded
--   - encoding: $\lceil k/2\rceil\le l\le n-\lfloor k/2\rfloor$ → `(k + 1) / 2 ≤ l` and `l + k / 2 ≤ n` in ℕ; reason: same condition on integers
--   - encoding: $\theta^{(n,l,k)}$ of Eq. (7) with footnote 7's binomial convention → `theta n l k q`, the printed sum in ℝ, terms with odd $k-r$ or $(k+r)/2>l$ set to $0$; reason: same value
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 14, §3.4.2, Eqs. (8) and (9)

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Kikuchi

namespace SmallSecretLWE.Classical

/-- §3.4.2, Eqs. (8) and (9). For natural numbers `n, l, k` and a positive integer `q`: if
`⌈k/2⌉ ≤ l ≤ n − ⌊k/2⌋` then
`θ^{(n,l,k)} ≥ (2^{k−1}/(k+1)) binom(n−k, l−⌈k/2⌉) (q−1)^{l−⌊k/2⌋}`; if `k ≤ l ≤ n` then
`θ^{(n,l,k)} ≥ 2^{1−k} binom(n−k, l−k) (q−1)^l`. Here `θ` is the right-hand side of Eq. (7). -/
theorem eqs_8_9 (n l k q : ℕ) (hq : 0 < q) :
    ((k + 1) / 2 ≤ l → l + k / 2 ≤ n →
      (2 : ℝ) ^ ((k : ℤ) - 1) / ((k : ℝ) + 1) * ((n - k).choose (l - (k + 1) / 2) : ℝ) *
          ((q : ℝ) - 1) ^ (l - k / 2) ≤ theta n l k q) ∧
    (k ≤ l → l ≤ n →
      (2 : ℝ) ^ (1 - (k : ℤ)) * ((n - k).choose (l - k) : ℝ) * ((q : ℝ) - 1) ^ l ≤
        theta n l k q) := by sorry

end SmallSecretLWE.Classical
