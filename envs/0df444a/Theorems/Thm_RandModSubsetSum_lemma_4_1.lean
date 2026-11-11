-- Prove2me | Theorems.Thm_RandModSubsetSum_lemma_4_1
-- name    : RandModSubsetSum.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:29.336229+00:00
-- url     : https://prove2.me/theorems/a92e172f-e7d4-4178-8de7-569883cf72fb
-- title:
--   Lemma 4.1 — a fixed representation matches all labels with probability $\prod_ip_i^{-(2^i-1)}$
-- statement:
--   In the auxiliary residue model with moduli $p_1,\dots,p_7$, every fixed representation $D$ of the root $x$ matches all residue labels with probability
--
--   $$p_{\rm match}=\prod_{i=1}^7p_i^{-(2^i-1)}.$$
--
--   Moreover, for all reals $K_1,\dots,K_7$ and $K_8=0$,
--   $$\alpha=\sum_{i=1}^7(2^i-1)(K_i-K_{i+1})=\sum_{i=1}^72^{i-1}K_i,$$
--   and if $|\log_2p_i-(K_i-K_{i+1})n|\le C_0$ for every $i$, then $|\log_2p_{\rm match}+\alpha n|\le 247\,C_0$, i.e. $p_{\rm match}=2^{-\alpha n+O(1)}$ (6).
--
--   Lemma 4.1 gives $\mathbb E(Z)=p_{\rm match}|\mathcal D|$, the first moment in the Chebyshev argument for $\Pr(Z=0)$.
--
--   Differences from the source:
--   - generalization: every fixed D ∈ 𝒟 (the exact-type family), distinct primes p_i → every representation D of x, any positive moduli p_i; reason: the counting argument uses neither the exact types nor primality; the source's case is a special case
--   - generalization: p_match = 2^{−αn+O(1)} → the exact product, the telescoping identity, and |log₂ p_match + αn| ≤ 247·C₀ under |log₂ p_i − (K_i − K_{i+1})n| ≤ C₀; reason: pins the O(1) (247 = Σ_{i=1}^7 (2^i − 1)); implies the printed form
--   - encoding: depths and slots 1-indexed, F_{p_i} → index i : Fin 7 for depth i+1, 0-indexed slots, residues as representatives in {0, …, p − 1}; reason: Lean convention; same instances
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Lemma 4.1 and (6), p. 19

import Mathlib
import Definitions.Def_RandModSubsetSum_Template

open scoped BigOperators

namespace RandModSubsetSum

/-- **Lemma 4.1** (matching probability). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Lemma 4.1 and (6), p. 19.

In the auxiliary residue model, every fixed representation `D` of the root `x` matches all
residue labels with probability `p_match = Π_{i=1}^7 p_i^{−(2^i − 1)} = 2^{−αn + O(1)}`, where
`α = Σ_{i=1}^7 (2^i − 1)(K_i − K_{i+1}) = Σ_{i=1}^7 2^{i−1} K_i` (`K_8 = 0`).

The statement has three parts: (1) the exact probability, for any positive moduli; (2) the
telescoping identity for every real `K_1, …, K_7`; (3) the `O(1)` form with the constant pinned: if
`|log₂ p_i − (K_i − K_{i+1}) n| ≤ C₀` for all `i`, then `|log₂ p_match + α n| ≤ 247 C₀`
(`247 = Σ_{i=1}^7 (2^i − 1)`).

**Formalization Note.** Index `i : Fin 7` stands for depth `i + 1`; `K i` is `K_{i+1}` and
`Knext K i` is `K_{i+2}` (`0` for the last). The moduli need only be positive: the paper's distinct
primes are a special case. -/
theorem lemma_4_1 {n : ℕ} (p : Fin 7 → ℕ) (hp : ∀ i, 0 < p i) (x : Fin n → Fin 2) (D : Rep n)
    (hD : IsRepOf x D) :
    auxProb p x (Matches D) = ∏ i : Fin 7, ((p i : ℝ) ^ (2 ^ (i.val + 1) - 1))⁻¹ ∧
    (∀ K : Fin 7 → ℝ, ∑ i : Fin 7, ((2 : ℝ) ^ (i.val + 1) - 1) * (K i - Knext K i) =
      ∑ i : Fin 7, (2 : ℝ) ^ i.val * K i) ∧
    (∀ (K : Fin 7 → ℝ) (C₀ : ℝ),
      (∀ i, |Real.logb 2 (p i) - (K i - Knext K i) * n| ≤ C₀) →
      |Real.logb 2 (∏ i : Fin 7, ((p i : ℝ) ^ (2 ^ (i.val + 1) - 1))⁻¹) +
          (∑ i : Fin 7, (2 : ℝ) ^ i.val * K i) * n| ≤ 247 * C₀) := by sorry

end RandModSubsetSum
