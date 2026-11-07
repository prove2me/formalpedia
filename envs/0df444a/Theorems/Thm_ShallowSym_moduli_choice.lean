-- Prove2me | Theorems.Thm_ShallowSym_moduli_choice
-- name    : ShallowSym.moduli_choice
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:16.806501+00:00
-- url     : https://prove2.me/theorems/6863a971-9745-488d-9059-87c49bd4e211
-- title:
--   The choice of moduli: $n^{1/(d-1)} < k_i \le p_i\,n^{1/(d-1)}$, pairwise coprime (corrected: $n\ge 1$ for the upper bound)
-- statement:
--   Let $d\ge 2$ and let $k_i$ ($i=1,\dots,d-1$) be the smallest power of the $i$-th prime $p_i$ that is greater than $n^{1/(d-1)}$. Then
--
--   1. $n^{1/(d-1)} < k_i$ for every $i$;
--   2. if $n\ge 1$, then for every $i$
--   $$k_i \le p_i\, n^{1/(d-1)};$$
--   3. the moduli $k_1,\dots,k_{d-1}$ are pairwise coprime.
--
--   Since $p_i$ depends on $d$ only, clause 2 gives $k_i=O(n^{1/(d-1)})$, which keeps the success probability of a random test at $2^{-O(n^{1/(d-1)})}$.
--
--   Differences from the source:
--   - correction: k_i ≤ p_i n^{1/(d−1)} for all n → the upper bound assumes n ≥ 1; reason: at n = 0, n^{1/(d−1)} = 0, the smallest power of p_i greater than 0 is p_i⁰ = 1, and 1 ≤ p_i · 0 is false
--   - reading: 'We can arrange this' (moduli pairwise coprime and greater than n^{1/(d−1)}, and not too much larger) → all three clauses: lower bound, upper bound, pairwise coprimality; reason: the sentence arranges the requirements of the preceding paragraph together with the new upper bound
--   - encoding: the i-th prime p_i, i = 1, …, d − 1 → Nat.nth Nat.Prime i with i : Fin (d − 1) (0-based, p₀ = 2); reason: Lean convention; same moduli
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §4 'Anatomy of a test', p.11

import Mathlib
import Definitions.Def_ShallowSym_modulus

namespace ShallowSym

/-- §4 "Anatomy of a test", p.11 (corrected: the upper bound needs `n ≥ 1`). V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"We can arrange this by making ki the smallest power of the ith prime pi that is greater than
n^{1/(d−1)}, in which case ki ≤ pi n^{1/(d−1)} = O(n^{1/(d−1)})."

For `d ≥ 2`, let `k_i` (`i = 0, …, d − 2`) be the smallest power of the `i`-th prime `p_i`
greater than `n^{1/(d−1)}` (`modulus`). Then
1. `n^{1/(d−1)} < k_i` for every `i`;
2. if `n ≥ 1`, then `k_i ≤ p_i · n^{1/(d−1)}` for every `i`;
3. the `k_i` are pairwise coprime.

**Formalization Note.** Correction: at `n = 0`, `n^{1/(d−1)} = 0`, the smallest power of `p_i`
greater than 0 is `p_i^0 = 1`, and `1 ≤ p_i · 0` is false; so clause 2 assumes `n ≥ 1`.
Pairwise coprimality is what the CRT display before this sentence requires of the moduli. The
primes are 0-based (`p_0 = 2`). The trailing `= O(n^{1/(d−1)})` follows from clause 2 because
`p_i` depends on `d` only. -/
theorem moduli_choice (d n : ℕ) (hd : 2 ≤ d) :
    (∀ i : Fin (d - 1), (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) - 1)) < (modulus d n i : ℝ)) ∧
    (1 ≤ n → ∀ i : Fin (d - 1),
      (modulus d n i : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) - 1))) ∧
    Pairwise (fun i j : Fin (d - 1) => Nat.Coprime (modulus d n i) (modulus d n j)) := by sorry

end ShallowSym
