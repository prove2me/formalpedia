-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_lemma_4_6
-- name    : RecoveryStorage3SUM.Adaptive.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:49.659781+00:00
-- url     : https://prove2.me/theorems/25e62a45-0b46-49f6-865c-571e0c679f88
-- title:
--   Lemma 4.6 — $|M_r|\le 2n^\delta\log^2 n$ except with probability $O(1/\log n)$
-- statement:
--   Let $A,B$ be sets of $n$ polynomially bounded integers, $0\le\delta<1$, $R$ a sample passing the coverage check, $c$ a polynomially bounded target and $r=c\bmod p$. For large $n$,
--   $$\Pr\big[|M_r|>2n^\delta\log^2 n\big]\le \frac{C}{\log n},$$
--   both for a uniform prime of the range and for the prime of an accepted attempt.
--
--   The bound on $|M_r|$ is the input to the isolation argument and to the reading cap.
--
--   Differences from the source:
--   - generalization: the bound over a run after its load check → both the fresh uniform-prime bound and the accepted-attempt bound; reason: the fresh bound is also established in the source proof; stating it alongside the conditional bound retains and extends the asserted conclusion
--   - reading: "over the runs randomness" → the bound for both a fresh prime and an accepted attempt; reason: the source leaves the law implicit; both readings are stated
--   - reading: "after a successful preprocessing every unmarked value is light" → fixed sample $R$ passing the coverage check of Algorithm 1; reason: that check runs before any run is drawn (line 2); its failure is bounded by Lemma 4.1
--   - encoding: integers bounded by $n^{O(1)}$ (standing assumption, §2) → $|x|\le H(n+2)^\kappa$ with $H,\kappa$ fixed first; reason: same class of inputs; constants are chosen after them
--   - encoding: real sizes $L=6n^\delta\log^2 n$, $|R|=3n^{1-\delta}$, prime range from $n^{2-\delta}\log^3 n$, "$L$ divides $n$" → $L=\lceil6n^\delta\log^2n\rceil$, $|R|=\min(\lceil3n^{1-\delta}\rceil,n)$, primes in $[P,2P)$ with $P=\lceil n^{2-\delta}\log^3n\rceil$, and parts of sizes $\lfloor n/L\rfloor$ or $\lceil n/L\rceil$; reason: integer rounding preserves the asymptotic bounds and isolation constants; it is exact on the integral simplifying regime; the sample cap is inactive for positive delta at large n and gives R=A at the otherwise undefined delta=0 sampler
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Lemma 4.6, p.12

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Laws

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

/-- Lemma 4.6, p.12: for a fixed target `c` and `r = c mod p`, one has `|M_r| ≤ 2 n^δ log² n` except with
probability `O(1 / log n)` over the run, both for the prime of a fresh attempt and for an accepted one. -/
theorem lemma_4_6 (H κ : ℕ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (cK : ℕ) (hcK : 1 ≤ cK) :
    ∃ (C : ℝ) (n₀ : ℕ), 0 < C ∧ ∀ (A B R : Finset ℤ) (c : ℤ), n₀ ≤ A.card → B.card = A.card →
      (∀ a ∈ A, PolyBounded H κ A.card a) → (∀ b ∈ B, PolyBounded H κ A.card b) →
      PolyBounded H κ A.card c → R ∈ sampleSpace A δ → HeavyCovered A B R δ →
      unifProb (primeSpace A.card δ)
          (fun p => 2 * heavyThreshold A.card δ <
            ((unmarkedClass A B R p (residue p c)).card : ℝ)) ≤ C / Real.log A.card ∧
      unifProb (passingAttempts A B R δ (logCount cK A.card) (numParts A.card δ))
          (fun x => 2 * heavyThreshold A.card δ <
            ((unmarkedClass A B R x.1 (residue x.1 c)).card : ℝ)) ≤ C / Real.log A.card := by sorry

end RecoveryStorage3SUM.Adaptive
