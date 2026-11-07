-- Prove2me | Theorems.Thm_ShallowSym_covering
-- name    : ShallowSym.covering
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:34.767027+00:00
-- url     : https://prove2.me/theorems/6fbfd7bc-2be5-4bad-90e3-c87334faa0bb
-- title:
--   Covering by random tests: expectation $\le 2^n(1-p)^T\le 2^n e^{-pT}<1$ (corrected: $T\ge 1$)
-- statement:
--   Let $\Omega$ be a finite nonempty set of tests, $X$ a finite set of at most $2^n$ inputs, and $0<p\le 1$ such that every $x\in X$ passes at least a $p$ fraction of the tests in $\Omega$. Draw $T$ tests independently and uniformly from $\Omega$. Then
--
--   1. the expected number of $x\in X$ that pass none of the $T$ tests is at most $2^n(1-p)^T$;
--   2. $2^n(1-p)^T\le 2^n\exp(-pT)$;
--   3. if $T\ge 1$ and $T\ge n/p$, then
--   $$2^n\exp(-pT)<1,$$
--   and there is a choice of $T$ tests such that every $x\in X$ passes at least one of them.
--
--   With $p=e^{-\sum_i k_i}=2^{-O(n^{1/(d-1)})}$ this gives the OR of $2^{O(n^{1/(d-1)})}$ tests computing $1[|x|=t]$.
--
--   **Formalization Note** A random choice of $T$ tests is a uniform tuple $\omega:\{0,\dots,T-1\}\to\Omega$, and the expectation is the average over all $|\Omega|^T$ tuples. Tests are given by an arbitrary relation `passes : Ω → α → Bool`.
--
--   Differences from the source:
--   - correction: 'less than 1 for T ≥ n/p' → the strict bound and the existence of a covering choice assume T ≥ 1; reason: at n = 0 and T = 0 (so T ≥ n/p) the bound is 2⁰(1 − p)⁰ = 1, not less than 1, and a nonempty X is not covered by zero tests
--   - generalization: the paper's random tests for |x| = t and its valid inputs x → any finite nonempty test set Ω, any relation passes, any finite X with |X| ≤ 2ⁿ; reason: specializes to the paper's tests, with X the inputs of weight t
--   - encoding: p a probability (p := e^{−Σ kᵢ}) → hypotheses 0 < p ≤ 1 and p·|Ω| ≤ #{ω : passes ω x} for x ∈ X; reason: the paper's p is a probability bound; same instances
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §4 'Coverage with random tests', pp.11–12; depth-3 version §3, p.9

import Mathlib

namespace ShallowSym

/-- §4 "Coverage with random tests", pp.11–12 (corrected: `T ≥ 1`); depth-3 version §3, p.9.
V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"With T independently chosen random tests, the expected number of valid inputs x that do not pass
any tests is at most 2^n(1 − p)^T ≤ 2^n exp(−pT) which is less than 1 for T ≥ n/p =
2^{O(n^{1/(d−1)})}. Thus, we can compute 1[|x| = t] with the OR of 2^{O(n^{1/(d−1)})} tests"

Let `Ω` be a finite nonempty set of tests, `X` a finite set of at most `2^n` valid inputs, and
`0 < p ≤ 1` such that every `x ∈ X` passes at least a `p` fraction of the tests. For `T` tests
drawn independently and uniformly from `Ω`:
1. the expected number of `x ∈ X` passing none of them is at most `2^n(1 − p)^T`;
2. `2^n(1 − p)^T ≤ 2^n exp(−pT)`;
3. if `T ≥ 1` and `pT ≥ n`, then `2^n exp(−pT) < 1`, and some choice of `T` tests is passed by
   every `x ∈ X` (some test passes each).

**Formalization Note.** Random tests are uniform `T`-tuples `ω : Fin T → Ω`, and the expectation
is the average over all `|Ω|^T` tuples. Correction: clause 3 needs `T ≥ 1`; at `n = 0`, `T = 0`
the expectation bound is `2^0(1 − p)^0 = 1`, which is not less than 1, and a nonempty `X` is not
covered by zero tests. `p ≤ 1` holds for the paper's probability `p` and makes `(1 − p)^T`
meaningful. The test family is arbitrary; the paper applies this to its tests for `|x| = t`. -/
theorem covering {Ω α : Type*} [Fintype Ω] [Nonempty Ω] (passes : Ω → α → Bool)
    (X : Finset α) (n : ℕ) (hX : X.card ≤ 2 ^ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hpass : ∀ x ∈ X,
      p * (Fintype.card Ω : ℝ) ≤ ((Finset.univ.filter (fun ω => passes ω x = true)).card : ℝ))
    (T : ℕ) :
    (∑ ω : Fin T → Ω, ((X.filter (fun x => ∀ i, passes (ω i) x = false)).card : ℝ)) /
        (Fintype.card Ω : ℝ) ^ T ≤ (2 : ℝ) ^ n * (1 - p) ^ T ∧
    (2 : ℝ) ^ n * (1 - p) ^ T ≤ (2 : ℝ) ^ n * Real.exp (-(p * T)) ∧
    (1 ≤ T → (n : ℝ) ≤ p * T →
      (2 : ℝ) ^ n * Real.exp (-(p * T)) < 1 ∧
        ∃ ω : Fin T → Ω, ∀ x ∈ X, ∃ i, passes (ω i) x = true) := by sorry

end ShallowSym
