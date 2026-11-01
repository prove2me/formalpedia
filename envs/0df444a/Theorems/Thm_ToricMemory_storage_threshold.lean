-- Prove2me | Theorems.Thm_ToricMemory_storage_threshold
-- name    : ToricMemory.storage_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:44.285975+00:00
-- url     : https://prove2.me/theorems/befad2ef-1285-4e15-86fb-17e97ed0d634
-- title:
--   Accuracy threshold of topological quantum memory: eqs. (60)–(64) (corrected: ≤ in (62))
-- statement:
--   Let $\mu_3$ be the connective constant of the cubic lattice, and write $\tilde p=p(1-p)$, $\tilde q=q(1-q)$. There are a constant $C>0$ and an integer $k\ge0$ such that the following hold.
--
--   1. (eq. (62) under (60)) For all $L,T\ge1$, all $p,q\in[0,1]$ with $\tilde p<(4\mu_3^2)^{-1}$ and $\tilde q<(4\mu_3^2)^{-1}$, and every maximum-likelihood decoder on the $L\times L\times T$ spacetime lattice,
--   $$
--   \mathrm{Prob}_{\rm fail}\;\le\;C\,(LT)^k\,(4\mu_3^2\tilde p)^{L/2}.
--   $$
--   2. ("eq. (60) is sufficient for reliable quantum storage") If $p,q\in[0,1]$ satisfy (60), storage is reliable: whenever $T$ grows at most polynomially in $L$, the failure probability of every maximum-likelihood decoder tends to $0$ as $L\to\infty$, uniformly over decoders.
--   3. (eq. (63)) If $p,q\in[0,1]$ and $\tilde p,\tilde q<(87.8)^{-1}$, storage is reliable.
--   4. (eq. (64)) If $0\le p,q<0.0114$, storage is reliable.
--
--   The threshold is the paper's one rigorous result: below it, minimum-weight decoding of the toric code with faulty syndrome measurements fails with probability decaying exponentially in $L$, and qubit and syndrome error rates below $1.14\%$ suffice.
--
--   Differences from the source:
--   - correction: Prob_fail < Q₃(L, T) · (4μ₃² p̃)^{L/2} (62) → Prob_fail ≤ C(LT)^k (√(4μ₃² p̃))^L; reason: false at p = 0 with any q ∈ (0, 1) satisfying (60): no horizontal link is ever in error or chosen by the decoder, so Prob_fail = 0 while the right side is 0; with an existential polynomial, ≤ and < are equivalent whenever p̃ > 0
--   - reading: E + E_min contains homologically nontrivial paths (p. 20) → E Δ E_min contains a cycle (empty boundary) with odd x-winding or odd y-winding (Fails); reason: on the 3-torus a cycle winding only in time has no horizontal link, while p. 20 says a damaging path has at least L horizontal links; the event contains the event that the class of E Δ E_min is nontrivial
--   - reading: μ₃ ≈ 4.684 (eq. (58)) → mu3 := inf_{n ≥ 1} c_n^{1/n}, the exact connective constant of ℤ³; reason: the decimal is the numerical value of the cubic lattice's connective constant, which is what the bound (58) is about
--   - reading: Prob_fail becomes arbitrarily small as L gets large, with T increasing no faster than a polynomial of L → ReliableStorage p q: for every T(L) with 1 ≤ T(L) ≤ C'L^{k'} and every ε > 0 there is L₀ with Prob_fail ≤ ε for all L ≥ max(L₀, 1) and every ML decoder; reason: the explicit quantifier form of the sentence; L₀ does not depend on the decoder
--   - generalization: E_min, the chain of maximal probability (44)–(46) with the observed boundary, ties broken randomly (p. 18), for error probabilities p, q → every map D returning, for each achievable boundary, a chain of maximal chainProb p q with that boundary (IsMLDecoder), for all p, q ∈ [0, 1]; reason: a random tie-break independent of E is a mixture of such maps, so the statement for every D specializes to the paper's decoder; chainProb has the same argmax as (44) for 0 < p, q < 1
--   - encoding: Q₃(L, T) a polynomial → C(LT)^k with C > 0 and k quantified before L, T, p, q and the decoder; reason: for L, T ≥ 1 every polynomial in (L, T) is bounded by such an expression
--   - encoding: (4μ₃²p̃)^{·/2} powers → (√x)^n for x^{n/2}; reason: the same real number for x ≥ 0; avoids ℕ division in the exponent
--   - encoding: bit-flip errors with plaquette syndromes and phase errors with site syndromes (p. 11) → one error type: independent link errors with probability p (horizontal) and q (vertical); reason: the two error types are recovered separately and are identical problems (p. 11)
--   - encoding: L, T positive integers → [NeZero L] [NeZero T]; reason: ZMod 0 = ℤ; excludes only the empty lattice
--   - reading: a spacetime lattice of L×L sites over T time slices, with L²T sites, 2L²T horizontal and L²T vertical links (Sec. V B–C, pp. 19–20) → the 3-torus ZMod L × ZMod L × ZMod T with periodic time; links are (site, direction) pairs; reason: the counts printed on p. 20 are exactly those of the 3-torus; an open-time slab has L²(T−1) vertical links
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V B–C, eqs. (60)–(64), p. 20; the 1.14% threshold is restated in Sec. I, p. 2

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_IsMLDecoder
import Definitions.Def_ToricMemory_Failure
import Definitions.Def_ToricMemory_CubicSAW

namespace ToricMemory

/-- **Accuracy threshold for topological quantum memory**, Dennis–Kitaev–Landahl–Preskill,
arXiv:quant-ph/0110143v1, Sec. V B–C, eqs. (60)–(64), p. 20 (PDF p. 20), with `≤` in (62).
There are `C > 0` and `k` such that:

1. (eq. (62) under (60)) for all `L, T ≥ 1`, all `p, q ∈ [0, 1]` with
   `p̃ = p(1 − p) < (4μ₃²)^{−1}` and `q̃ = q(1 − q) < (4μ₃²)^{−1}`, and every maximum-likelihood
   decoder `D`, `Prob_fail ≤ C (L T)^k (4μ₃² p̃)^{L/2}`;
2. ("eq. (60) is sufficient for reliable quantum storage") under (60), storage is reliable;
3. (eq. (63)) if `p̃, q̃ < (87.8)^{−1}`, storage is reliable;
4. (eq. (64)) if `p, q < .0114`, storage is reliable.

**Formalization Note** The polynomial `Q₃(L, T)` is encoded as `C (L T)^k`, with `C, k` fixed
before `L, T, p, q` and the decoder; `x^{L/2}` is `(√x)^L`; `μ₃` is the exact connective
constant `mu3`. The printed `<` in (62) fails at `p = 0`, where both sides vanish. -/
theorem storage_threshold :
    ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧
      (∀ (L T : ℕ) [NeZero L] [NeZero T] (p q : ℝ), 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
          p * (1 - p) < 1 / (4 * mu3 ^ 2) → q * (1 - q) < 1 / (4 * mu3 ^ 2) →
          ∀ D : Finset (Site L T) → Finset (Link L T), IsMLDecoder p q D →
            probFail p q D ≤
              C * ((L : ℝ) * T) ^ k * Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ L) ∧
      (∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
          p * (1 - p) < 1 / (4 * mu3 ^ 2) → q * (1 - q) < 1 / (4 * mu3 ^ 2) →
          ReliableStorage p q) ∧
      (∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
          p * (1 - p) < 1 / 87.8 → q * (1 - q) < 1 / 87.8 → ReliableStorage p q) ∧
      (∀ p q : ℝ, 0 ≤ p → p < 0.0114 → 0 ≤ q → q < 0.0114 → ReliableStorage p q) := by sorry

end ToricMemory
