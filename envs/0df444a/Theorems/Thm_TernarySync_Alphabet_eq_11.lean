-- Prove2me | Theorems.Thm_TernarySync_Alphabet_eq_11
-- name    : TernarySync.Alphabet.eq_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:54:40.2552+00:00
-- url     : https://prove2.me/theorems/da034643-e275-42c0-8c65-48337cf23a85
-- title:
--   Eq. (11) — deletion-witness count $|B_\ell(y)| \le \sum_{0 \le d < \eta\ell} \binom{\ell}{d}^2 q^d$
-- statement:
--   Let $\Sigma$ be a finite alphabet of size $q$, let $\eta = 1/1000$, let $\ell > 1000$ be an integer and let $y \in \Sigma^\ell$ be a fixed word. The deletion ball $B_\ell(y)$ is the set of words of length $\ell$ whose longest common subsequence with $y$ exceeds $(1-\eta)\ell$, and
--
--   $$|B_\ell(y)| = \big|\{x \in \Sigma^\ell : \mathrm{LCS}(x,y) > (1-\eta)\ell\}\big| \le \sum_{0 \le d < \eta\ell} \binom{\ell}{d}^2 q^d. \tag{11}$$
--
--   This standard count bounds the number of near matches of a fixed neighbour; it is the candidate side of the probability comparison in the proof of Theorem 4.1.
--
--   **Formalization Note.** The alphabet is any `Fintype β` and $q$ is its cardinality; $|B_\ell(y)|$ is `Set.ncard` of `delBall (1/1000) ℓ y` (a finite set); the sum runs over the naturals $d \le \ell$ with $d < \ell/1000$, which are exactly the $d$ with $0 \le d < \eta\ell$.
--
--   Differences from the source:
--   - encoding: an alphabet Σ of size q; 0 ≤ d < ηℓ → a Fintype β with q = Fintype.card β; d ranging over range (ℓ + 1) filtered by d < ℓ/1000; reason: d < ηℓ < ℓ already forces d ≤ ℓ, so the range is the same
--   - encoding: the standing setting of §4: η = 1/1000, an integer ℓ > L = 1000, a fixed neighbour y of length ℓ → η = 1/1000 as a literal, hypotheses 1000 < ℓ and y.length = ℓ; reason: the section's standing assumptions written as binders
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 16 (PDF 17), §4, Eq. (11)

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Equation (11) (p. 16), the deletion-witness count: over any finite alphabet `β` of size `q`,
for `η = 1/1000`, an integer `ℓ > 1000` and a fixed word `y` of length `ℓ`,
`|B_ℓ(y)| = |{x ∈ β^ℓ : LCS(x, y) > (1 − η)ℓ}| ≤ ∑_{0 ≤ d < ηℓ} C(ℓ, d)^2 q^d`. -/
theorem eq_11 {β : Type*} [Fintype β] (ℓ : ℕ) (hℓ : 1000 < ℓ) (y : List β) (hy : y.length = ℓ) :
    ((delBall ((1 : ℝ) / 1000) ℓ y).ncard : ℝ) ≤
      ∑ d ∈ (Finset.range (ℓ + 1)).filter (fun d : ℕ => (d : ℝ) < (1 : ℝ) / 1000 * (ℓ : ℝ)),
        ((ℓ.choose d : ℝ) ^ 2 * (Fintype.card β : ℝ) ^ d) := by sorry

end TernarySync.Alphabet
