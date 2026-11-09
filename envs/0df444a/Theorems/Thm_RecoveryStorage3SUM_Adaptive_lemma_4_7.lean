-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_lemma_4_7
-- name    : RecoveryStorage3SUM.Adaptive.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:30.825828+00:00
-- url     : https://prove2.me/theorems/2bbfbb53-cb2a-417d-aaec-4e77b10b4269
-- title:
--   Lemma 4.7 — every first coordinate of $M_r$ enters $\widehat A$
-- statement:
--   Let $A,B$ be sets of $n$ polynomially bounded integers, $0\le\delta<1$, $R$ a sample passing the heavy-coverage check, and $c$ a polynomially bounded target. Take $K=\lceil c_K\log n\rceil$ for $c_K$ sufficiently large. Draw a run from the accepted-attempt law, conditional on
--   $$|M_r|\le 2n^\delta\log^2 n,\qquad r=c\bmod p.$$
--   For inverters each correct except with probability $\eta$, every fixed $d>0$ and all sufficiently large $n$,
--   $$\Pr\big[\text{some first coordinate of }M_r\text{ is not in }\widehat A\big]\le n^{-d}+KL\eta.$$
--   The probability includes the conditional run and the inverter coins. The run has passed the load check; no independence of its accepted partitions is assumed.
--
--   Differences from the source:
--   - generalization: randomness of the FN structures of Lemma 2.3 → any probability space with failure at most $\eta$ per structure, adding a term $\eta$ per structure to the bound; reason: the coins of Lemma 2.3 are an instance, with $\eta$ polynomially small, which gives the sources "w.h.p."
--   - reading: "with high probability" → for every fixed exponent $d>0$, failure at most $n^{-d}$ for $n\ge n_0$; reason: pp.10-13 give tunable polynomial tails
--   - reading: "Condition on $|M_r|\le2n^\delta\log^2 n$", for the run of Algorithm 1 → the uniform law on load-passing attempts further conditioned on $|M_{c\bmod p}|\le2n^\delta\log^2 n$; reason: this retains the actual accepted-run law; rejection can change the joint prime and partition distribution
--   - reading: "after a successful preprocessing every unmarked value is light" → fixed sample $R$ passing the coverage check of Algorithm 1; reason: that check runs before any run is drawn (line 2); its failure is bounded by Lemma 4.1
--   - encoding: integers bounded by $n^{O(1)}$ (standing assumption, §2) → $|x|\le H(n+2)^\kappa$ with $H,\kappa$ fixed first; reason: same class of inputs; constants are chosen after them
--   - encoding: real sizes $L=6n^\delta\log^2 n$, $|R|=3n^{1-\delta}$, prime range from $n^{2-\delta}\log^3 n$, "$L$ divides $n$" → $L=\lceil6n^\delta\log^2n\rceil$, $|R|=\min(\lceil3n^{1-\delta}\rceil,n)$, primes in $[P,2P)$ with $P=\lceil n^{2-\delta}\log^3n\rceil$, and parts of sizes $\lfloor n/L\rfloor$ or $\lceil n/L\rceil$; reason: integer rounding preserves the asymptotic bounds and isolation constants; it is exact on the integral simplifying regime; the sample cap is inactive for positive delta at large n and gives R=A at the otherwise undefined delta=0 sampler
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Lemma 4.7, p.12

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Laws

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

open MeasureTheory Classical in
/-- Lemma 4.7, p.12: fix a target `c` and a coverage-passing sample `R`. Condition the accepted-run
law on `|M_r| ≤ 2 n^δ log² n`, where `r = c mod p`. Except with probability `n^{-d} + KLη` over
that conditional run and its inverter coins, every first coordinate of `M_r` enters `Â`.
Acceptance includes the load check; the conditioned partitions are not asserted independent. -/
theorem lemma_4_7 (H κ : ℕ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (d : ℝ) (hd : 0 < d) :
    ∃ cK₀ : ℕ, ∀ cK : ℕ, cK₀ ≤ cK → ∃ n₀ : ℕ, ∀ (A B R : Finset ℤ) (c : ℤ),
      n₀ ≤ A.card → B.card = A.card →
      (∀ a ∈ A, PolyBounded H κ A.card a) → (∀ b ∈ B, PolyBounded H κ A.card b) →
      PolyBounded H κ A.card c → R ∈ sampleSpace A δ → HeavyCovered A B R δ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (build : Fin (logCount cK A.card) × Fin (numParts A.card δ) → ℕ → (ℕ → ℕ) → Ω → ℕ → Option ℕ)
        (η : ℝ), 0 ≤ η → InverterLaw μ build η →
        unifAvg ((passingAttempts A B R δ (logCount cK A.card) (numParts A.card δ)).filter
              fun x => ((unmarkedClass A B R x.1 (residue x.1 c)).card : ℝ) ≤
                2 * heavyThreshold A.card δ)
            (fun x => μ.real {ω | ¬ ∀ ab ∈ unmarkedClass A B R x.1 (residue x.1 c),
              ab.1 ∈ discovered B R (toRun x) (runInverters B R build (toRun x) ω) (residue x.1 c)}) ≤
          (A.card : ℝ) ^ (-d) + (logCount cK A.card : ℝ) * (numParts A.card δ : ℝ) * η := by sorry

end RecoveryStorage3SUM.Adaptive
