-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_lemma_4_4
-- name    : RecoveryStorage3SUM.Adaptive.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:04.489634+00:00
-- url     : https://prove2.me/theorems/c3ce3cf4-1902-47fc-9936-3794d562a36d
-- title:
--   Lemma 4.4 — every possible target has at least $J/2$ clean runs
-- statement:
--   Let $A,B$ be sets of $n$ polynomially bounded integers, $0\le\delta<1$, and $R$ a sample passing the coverage check. Let $J=\lceil c_J\log n\rceil$ and $K=\lceil c_K\log n\rceil$ with $c_J,c_K\ge1$. For every $d>0$ and large $n$, over $J$ accepted runs, independent given $R$,
--   $$\Pr\big[\exists\,c\text{ polynomially bounded with fewer than }J/2\text{ clean runs}\big]\le n^{-d}.$$
--
--   Clean runs are those in which the class of $c$ holds no other marked value, so that the modular count can be corrected exactly.
--
--   Differences from the source:
--   - reading: "with high probability" → for every fixed exponent $d>0$, failure at most $n^{-d}$ for $n\ge n_0$; reason: pp.10-13 give tunable polynomial tails
--   - reading: "the run", redrawn on a failed load check → uniform on attempts passing the load check, independent across runs given $R$; reason: this is exactly the conditional law of an accepted attempt; exhausting the attempts is the separate failure of line 7
--   - reading: "after a successful preprocessing every unmarked value is light" → fixed sample $R$ passing the coverage check of Algorithm 1; reason: that check runs before any run is drawn (line 2); its failure is bounded by Lemma 4.1
--   - encoding: integers bounded by $n^{O(1)}$ (standing assumption, §2) → $|x|\le H(n+2)^\kappa$ with $H,\kappa$ fixed first; reason: same class of inputs; constants are chosen after them
--   - encoding: real sizes $L=6n^\delta\log^2 n$, $|R|=3n^{1-\delta}$, prime range from $n^{2-\delta}\log^3 n$, "$L$ divides $n$" → $L=\lceil6n^\delta\log^2n\rceil$, $|R|=\min(\lceil3n^{1-\delta}\rceil,n)$, primes in $[P,2P)$ with $P=\lceil n^{2-\delta}\log^3n\rceil$, and parts of sizes $\lfloor n/L\rfloor$ or $\lceil n/L\rceil$; reason: integer rounding preserves the asymptotic bounds and isolation constants; it is exact on the integral simplifying regime; the sample cap is inactive for positive delta at large n and gives R=A at the otherwise undefined delta=0 sampler
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Lemma 4.4, p.11

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Laws

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

open Classical in
/-- Lemma 4.4, p.11: with high probability over `J` accepted runs (independent given `R`), every
possible target, simultaneously, has at least `J/2` clean runs. -/
theorem lemma_4_4 (H κ : ℕ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (d : ℝ) (hd : 0 < d)
    (cJ cK : ℕ) (hcJ : 1 ≤ cJ) (hcK : 1 ≤ cK) :
    ∃ n₀ : ℕ, ∀ A B R : Finset ℤ, n₀ ≤ A.card → B.card = A.card →
      (∀ a ∈ A, PolyBounded H κ A.card a) → (∀ b ∈ B, PolyBounded H κ A.card b) →
      R ∈ sampleSpace A δ → HeavyCovered A B R δ →
      unifProb (acceptedRuns A B R δ (logCount cJ A.card) (logCount cK A.card) (numParts A.card δ))
        (fun runs => ¬ ∀ c : ℤ, PolyBounded H κ A.card c →
          logCount cJ A.card ≤ 2 * (Finset.univ.filter fun j => CleanFor B R (runs j).1 c).card) ≤
        (A.card : ℝ) ^ (-d) := by sorry

end RecoveryStorage3SUM.Adaptive
