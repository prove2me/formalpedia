-- Prove2me | Theorems.Thm_QuantumPRC_theorem_8_13
-- name    : QuantumPRC.theorem_8_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:50.196427+00:00
-- url     : https://prove2.me/theorems/3bea6e4d-dc19-4af8-a54f-a7af64abe380
-- title:
--   Theorem 8.13 — GraphSample outputs a $(t(n),d(n))$-good graph with overwhelming probability, with the bound (238)
-- statement:
--   Let $p>0$, let $\gamma$ be a positive rational with $\gamma\le\min\{2^{-32},p/2\}$, and let $t(n)=o(n\log\log n/\log n)$. Let $d(n)$ be given by (220) and let $G$ be the output of Construction 8.10 on $1^n$ ($d(n)$ independent uniform permutations of $[n]$). Then:
--
--   1. there is a negligible $\nu$ such that, for all sufficiently large $n$ and every $v\in\{0,1\}^{2n}$ with $\mathrm{wt}(v)\le t(n)$,
--   $$
--   \Pr_{G\leftarrow\mathsf{GraphSample}(1^n)}\big[G\text{ is }(t(n),d(n))\text{-good for }v\big]\ge1-\nu(n);
--   $$
--   2. for all sufficiently large $n$ and every such $v$, the explicit bound (238) holds:
--   $$
--   \Pr\big[G\text{ is }(t(n),d(n))\text{-good for }v\big]\ge1-4t\Big(\frac dn\Big)^{d/16}-2n\Big(\frac{16e\,t}{n}\Big)^{d/16}.
--   $$
--
--   Together with Theorem 8.9 this gives the recovery guarantee (ii) of Theorem 7.1.
--
--   Differences from the source:
--   - generalization: the conclusion ≥ 1 − negl(n) → adds, as a second conjunct, the explicit bound (238) for all sufficiently large n; reason: (238) is the bound the paper's proof establishes (p.61); the first conjunct is the printed theorem
--   - reading: for all sufficiently large n and every v … ≥ 1 − negl(n) → one negligible function for all v; reason: the stronger of the two readings; the proof's bound (238) does not depend on v
--   - encoding: d(n) = 16⌊min{⌈log₂(2n)⌉², γn/t(n)}/16⌋ → the same with γn/0 = 0, so d(n) = 0 (the empty graph) when t(n) = 0; reason: Lean convention; at t(n) = 0 every v has weight 0 and the empty graph is (0, 0)-good
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 8.13, p.59; Eq. (220), p.58; Construction 8.10, p.59; Eq. (238), p.61

import Mathlib
import Definitions.Def_QuantumPRC_GraphRecoverSpec

open Filter Asymptotics

namespace QuantumPRC

/-- **Theorem 8.13** (sampling a graph good for a fixed perturbation), with the bound (238).
Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), Theorem 8.13, p.59: "For all sufficiently large
`n` and every `v ∈ {0,1}^{2n}` with `wt(v) ≤ t(n)`, `Pr_{G←GraphSample(1^n)}[G is (t(n), d(n))-good for v] ≥
1 − negl(n)`." Standing assumptions (Theorem 7.1, p.40, and §8.3, p.58): a constant `p > 0`,
`t(n) = o(n log log n / log n)` (107), a positive rational `γ ≤ min{2^{−32}, p/2}`, and `d(n)` from (220).
The proof establishes, for all sufficiently large `n`, Eq. (238), p.61:
`Pr[G is (t(n), d(n))-good for v] ≥ 1 − 4t(d/n)^{d/16} − 2n(16e t/n)^{d/16}`.

**Formalization Note.** GraphSample is the exact law of Construction 8.10 (`d(n)` independent uniform
permutations, `goodProb`). The negligible function is uniform in `v`. `d(n)` is a multiple of `16`, so
`d/16` is a natural exponent. -/
theorem theorem_8_13 (p : ℝ) (hp : 0 < p) (γ : ℚ) (hγ : 0 < γ) (hγ1 : (γ : ℝ) ≤ 2⁻¹ ^ 32)
    (hγ2 : (γ : ℝ) ≤ p / 2) (t : ℕ → ℕ)
    (ht : (fun n => (t n : ℝ)) =o[atTop] radiusScale) :
    (∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ᶠ n in atTop, ∀ v : Bits (2 * n), wt v ≤ t n →
      1 - ν n ≤ goodProb γ t n v) ∧
    (∀ᶠ n in atTop, ∀ v : Bits (2 * n), wt v ≤ t n →
      1 - 4 * (t n : ℝ) * ((degParam γ t n : ℝ) / n) ^ (degParam γ t n / 16) -
          2 * (n : ℝ) * (16 * Real.exp 1 * t n / n) ^ (degParam γ t n / 16) ≤
        goodProb γ t n v) := by sorry

end QuantumPRC
