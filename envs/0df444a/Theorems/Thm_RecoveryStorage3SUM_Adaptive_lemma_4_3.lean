-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_lemma_4_3
-- name    : RecoveryStorage3SUM.Adaptive.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:14.606071+00:00
-- url     : https://prove2.me/theorems/2b67aec6-9d07-4c7e-b7a1-356bba59b8c5
-- title:
--   Lemma 4.3 — the expected squared load of one partition is at most $2n^2$
-- statement:
--   Let $A,B$ be sets of $n$ polynomially bounded integers, $0\le\delta<1$, and $R$ a sample passing the coverage check. For large $n$, for a uniform prime $p$ of the range and an independent uniform balanced partition into $L$ parts,
--   $$\mathbb E_{p,\pi}\Big[\sum_{i\in[L]}\sum_{r\in[p]}d_{i,r}^2\Big]\le 2n^2.$$
--
--   By Markov's inequality this makes the load check pass with high probability, which is what controls the size of the inverters.
--
--   Differences from the source:
--   - reading: "after a successful preprocessing every unmarked value is light" → fixed sample $R$ passing the coverage check of Algorithm 1; reason: that check runs before any run is drawn (line 2); its failure is bounded by Lemma 4.1
--   - encoding: integers bounded by $n^{O(1)}$ (standing assumption, §2) → $|x|\le H(n+2)^\kappa$ with $H,\kappa$ fixed first; reason: same class of inputs; constants are chosen after them
--   - encoding: real sizes $L=6n^\delta\log^2 n$, $|R|=3n^{1-\delta}$, prime range from $n^{2-\delta}\log^3 n$, "$L$ divides $n$" → $L=\lceil6n^\delta\log^2n\rceil$, $|R|=\min(\lceil3n^{1-\delta}\rceil,n)$, primes in $[P,2P)$ with $P=\lceil n^{2-\delta}\log^3n\rceil$, and parts of sizes $\lfloor n/L\rfloor$ or $\lceil n/L\rceil$; reason: integer rounding preserves the asymptotic bounds and isolation constants; it is exact on the integral simplifying regime; the sample cap is inactive for positive delta at large n and gives R=A at the otherwise undefined delta=0 sampler
--   - reading: the bound as stated, with no threshold on $n$ → for $n\ge n_0$; reason: the proof bounds terms with $O$-constants by $n^2/3$, which needs large $n$
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Lemma 4.3, p.11

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Laws

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

/-- Lemma 4.3, p.11: for one partition, `E[∑_{i,r} d_{i,r}²] ≤ 2n²`, jointly over the prime and the
partition, on a fixed sample `R` that passed the heavy-coverage check of Algorithm 1. -/
theorem lemma_4_3 (H κ : ℕ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) :
    ∃ n₀ : ℕ, ∀ A B R : Finset ℤ, n₀ ≤ A.card → B.card = A.card →
      (∀ a ∈ A, PolyBounded H κ A.card a) → (∀ b ∈ B, PolyBounded H κ A.card b) →
      R ∈ sampleSpace A δ → HeavyCovered A B R δ →
      unifAvg (primeSpace A.card δ ×ˢ balancedSpace A (numParts A.card δ))
          (fun x => (squaredLoad B R x.1 x.2 : ℝ)) ≤ 2 * (A.card : ℝ) ^ 2 := by sorry

end RecoveryStorage3SUM.Adaptive
