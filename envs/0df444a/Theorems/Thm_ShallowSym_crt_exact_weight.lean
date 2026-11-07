-- Prove2me | Theorems.Thm_ShallowSym_crt_exact_weight
-- name    : ShallowSym.crt_exact_weight
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:07.196332+00:00
-- url     : https://prove2.me/theorems/0199d881-6dd7-4ed5-84e1-685814dfa2de
-- title:
--   Pairwise coprime moduli greater than $n^{1/(d-1)}$ pin down the weight
-- statement:
--   Let $d\ge 2$ and let $k_1,\dots,k_{d-1}$ be pairwise coprime natural numbers, each greater than $n^{1/(d-1)}$. Then
--
--   $$\prod_{i=1}^{d-1} k_i > n,$$
--
--   and for every target weight $t\in\{0,1,\dots,n\}$ and every $x\in\{0,1\}^n$,
--
--   $$\bigwedge_{i=1}^{d-1} 1\big[|x|\equiv t\pmod{k_i}\big] = 1\big[|x|=t\big].$$
--
--   So the AND of one test per modulus certifies the exact weight $t$.
--
--   Differences from the source:
--   - encoding: t a weight of the decomposition (1), t ∈ S ⊆ {0, 1, …, n} → hypothesis t ≤ n; reason: it excludes only t outside the paper's range; without it the display fails (n = 1, d = 2, k₁ = 2, t = 2, x = 0)
--   - encoding: moduli k₁, …, k_{d−1}; n^{1/(d−1)} → k : Fin (d − 1) → ℕ (0-based); the real power (n : ℝ) ^ (1 / ((d : ℝ) − 1)); reason: Lean convention; same instances
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §4 'Anatomy of a test', display after eq. (6), p.11

import Mathlib
import Definitions.Def_ShallowSym_weight

namespace ShallowSym

/-- §4 "Anatomy of a test", display after (6), p.11. V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"If the moduli are all pairwise coprime and greater than n^{1/(d−1)}, their product is greater
than n, and so ⋀_{i=1}^{d−1} 1[|x| ≡ t (mod ki)] = 1[|x| = t]."

Let `d ≥ 2` and let `k_1, …, k_{d−1}` be pairwise coprime natural numbers, each greater than
`n^{1/(d−1)}`. Then `∏ k_i > n`, and for every target weight `t ∈ {0, …, n}` and every
`x ∈ {0,1}^n`: `|x| ≡ t (mod k_i)` for all `i` iff `|x| = t`.

**Formalization Note.** `t ≤ n` is the context of the display (`t ∈ S ⊆ {0, …, n}`, eq. (1));
without it the identity fails (`n = 1`, `d = 2`, `k_1 = 2`, `t = 2`, `x = 0`). Moduli are
indexed by `Fin (d − 1)` (0-based); `n^{1/(d−1)}` is a real power. -/
theorem crt_exact_weight (d : ℕ) (hd : 2 ≤ d) (n t : ℕ) (ht : t ≤ n) (k : Fin (d - 1) → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (k i) (k j)))
    (hk : ∀ i, (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) - 1)) < (k i : ℝ)) :
    n < ∏ i, k i ∧ ∀ x : Cube n, (∀ i, weight x ≡ t [MOD k i]) ↔ weight x = t := by sorry

end ShallowSym
