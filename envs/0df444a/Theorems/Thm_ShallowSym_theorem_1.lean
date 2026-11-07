-- Prove2me | Theorems.Thm_ShallowSym_theorem_1
-- name    : ShallowSym.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:21.602584+00:00
-- url     : https://prove2.me/theorems/fccae917-82ec-4f5f-b3e5-f8bd34bb76e2
-- title:
--   Theorem 1 — every symmetric function has $\Sigma_d$ and $\Pi_d$ formulas of size $2^{O(n^{1/(d-1)})}$
-- statement:
--   For every constant $d\ge 2$ there is a constant $C>0$, depending on $d$ only, such that for every $n$ and every symmetric function $f:\{0,1\}^n\to\{0,1\}$ there are a $\Sigma_d$ formula and a $\Pi_d$ formula computing $f$, each with at most
--
--   $$2^{\,C\,(n+1)^{1/(d-1)}}$$
--
--   AND/OR gates. In words: every symmetric function on $n$ variables, in particular Majority, has depth-$d$ circuits of size $2^{O(n^{1/(d-1)})}$.
--
--   Together with Håstad's lower bound $2^{\Omega(n^{1/(d-1)})}$ for Parity and Majority, this determines the depth-$d$ circuit size of Majority up to the constant in the exponent.
--
--   **Formalization Note** Formulas are strictly layered alternating AND/OR trees over literals (`ShallowSym.Layer`): every literal sits at depth exactly $d$, a gate at level $\ell$ reads only nodes of level $\ell-1$, gates of arbitrary (also empty) fan-in, size = number of gates. The bound uses real powers, and $C$ is chosen after $d$ and before $n$ and $f$.
--
--   Differences from the source:
--   - generalization: depth-d circuits (DAGs with alternating layers) → depth-d formulas (trees, ShallowSym.Layer); reason: a formula is a circuit with the same number of gates, so the formula statement implies the circuit statement
--   - generalization: 'has depth-d circuits' → both a Σd and a Πd formula; reason: the proof establishes both (p.10, 'every symmetric function has Σd and Πd circuits'); either one gives the source's claim
--   - encoding: size 2^{O(n^{1/(d−1)})}, constants depending on d only (p.5) → ∃ C > 0 after d, before n and f, size ≤ 2^{C·(n+1)^{1/(d−1)}} for every n; reason: for n ≥ 1, (n+1)^{1/(d−1)} ≤ 2·n^{1/(d−1)}, so this is the usual reading with constant 2C; the (n+1) form also covers n = 0 without a threshold
--   - encoding: gates of arbitrary fan-in → empty gates allowed (empty AND = true, empty OR = false); reason: for n ≥ 1 each empty gate at level ℓ ≤ d can be replaced by a gadget of at most d gates over x₁, ¬x₁ computing the same constant, a d-dependent factor that C absorbs; at n = 0 the paper's model has no circuits at all
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), Theorem 1, p.10 (also p.2)

import Mathlib
import Definitions.Def_ShallowSym_IsSymmetric
import Definitions.Def_ShallowSym_Layer

namespace ShallowSym

/-- **Theorem 1**, p.10 (also stated on p.2). V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"For any constant d ≥ 2, every symmetric function on n variables has depth-d circuits of size
2^{O(n^{1/(d−1)})}."

For every `d ≥ 2` there is a constant `C > 0` (depending on `d` only) such that every symmetric
`f : {0,1}^n → {0,1}`, for every `n`, is computed both by a Σ_d formula and by a Π_d formula
with at most `2^{C·(n+1)^{1/(d−1)}}` AND/OR gates.

**Formalization Note.**
* Formulas are strictly layered alternating AND/OR trees over literals (`Layer`); a formula is
  a circuit with the same number of gates, so this implies the statement for circuits.
* Both a Σ_d and a Π_d formula are asserted, as the proof establishes (p.10, "We will show by
  induction on d that every symmetric function has Σd and Πd circuits").
* `2^{O(n^{1/(d−1)})}`, with the constant depending on `d` only (p.5), is written
  `2^{C·(n+1)^{1/(d−1)}}` with real powers and `∃ C` after `d` and before `n, f`; for
  `n ≥ 1`, `(n+1)^a ≤ 2·n^a`, so this is the usual reading, and it also covers `n = 0`.
* Empty gates are allowed (empty AND = true, empty OR = false). -/
theorem theorem_1 :
    ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Cube n → Bool), IsSymmetric f →
      (∃ φ : Layer n d, (∀ x, evalSigma d φ x = f x) ∧
        (size d φ : ℝ) ≤ (2 : ℝ) ^ (C * ((n : ℝ) + 1) ^ ((1 : ℝ) / ((d : ℝ) - 1)))) ∧
      (∃ ψ : Layer n d, (∀ x, evalPi d ψ x = f x) ∧
        (size d ψ : ℝ) ≤ (2 : ℝ) ^ (C * ((n : ℝ) + 1) ^ ((1 : ℝ) / ((d : ℝ) - 1)))) := by sorry

end ShallowSym
