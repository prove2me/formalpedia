-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_lemma_4_10
-- name    : RecoveryStorage3SUM.Adaptive.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:48.159224+00:00
-- url     : https://prove2.me/theorems/a42b778a-0ace-42c4-98ae-0b7aaf332123
-- title:
--   Lemma 4.10 — a clean accepted run recovers all of $M_r$ except with probability $O(1/\log n)$
-- statement:
--   Let $A,B$ be sets of $n$ polynomially bounded integers, $0\le\delta<1$, $R$ a sample passing the coverage check, and $c$ a polynomially bounded target. Take $K=\lceil c_K\log n\rceil$ for $c_K$ large, and inverters each correct except with probability $\eta$. Draw an attempt uniformly among those passing the load check and clean for $c$, and let $r=c\bmod p$. For large $n$,
--   $$\Pr\big[\mathrm{Recover}(r)\ne M_r\big]\le \frac{C}{\log n}+KL\eta.$$
--
--   Together with the abundance of clean runs, this yields a run that is exact for every target.
--
--   Differences from the source:
--   - generalization: randomness of the FN structures of Lemma 2.3 → any probability space with failure at most $\eta$ per structure, adding a term $\eta$ per structure to the bound; reason: the coins of Lemma 2.3 are an instance, with $\eta$ polynomially small, which gives the sources "w.h.p."
--   - reading: "Fix a target $c$ and a run that is clean for $c$ and passed the load check" → the uniform law on attempts with both properties; reason: this is the fresh law conditioned on those events
--   - reading: "after a successful preprocessing every unmarked value is light" → fixed sample $R$ passing the coverage check of Algorithm 1; reason: that check runs before any run is drawn (line 2); its failure is bounded by Lemma 4.1
--   - encoding: integers bounded by $n^{O(1)}$ (standing assumption, §2) → $|x|\le H(n+2)^\kappa$ with $H,\kappa$ fixed first; reason: same class of inputs; constants are chosen after them
--   - encoding: real sizes $L=6n^\delta\log^2 n$, $|R|=3n^{1-\delta}$, prime range from $n^{2-\delta}\log^3 n$, "$L$ divides $n$" → $L=\lceil6n^\delta\log^2n\rceil$, $|R|=\min(\lceil3n^{1-\delta}\rceil,n)$, primes in $[P,2P)$ with $P=\lceil n^{2-\delta}\log^3n\rceil$, and parts of sizes $\lfloor n/L\rfloor$ or $\lceil n/L\rceil$; reason: integer rounding preserves the asymptotic bounds and isolation constants; it is exact on the integral simplifying regime; the sample cap is inactive for positive delta at large n and gives R=A at the otherwise undefined delta=0 sampler
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Lemma 4.10, p.13

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Laws

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

open MeasureTheory Classical in
/-- Lemma 4.10, p.13: fix a target `c`. For a uniform attempt among those that pass the load check and
are clean for `c`, and the coins of its `KL` inverters, `Recover(r)` outputs all of `M_r`, `r = c mod p`,
except with probability `O(1 / log n) + KLη`; `η` bounds the failure probability of one inverter. -/
theorem lemma_4_10 (H κ : ℕ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) :
    ∃ cK₀ : ℕ, ∀ cK : ℕ, cK₀ ≤ cK → ∃ (C : ℝ) (n₀ : ℕ), 0 < C ∧
      ∀ (A B R : Finset ℤ) (c : ℤ), n₀ ≤ A.card → B.card = A.card →
      (∀ a ∈ A, PolyBounded H κ A.card a) → (∀ b ∈ B, PolyBounded H κ A.card b) →
      PolyBounded H κ A.card c → R ∈ sampleSpace A δ → HeavyCovered A B R δ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (build : Fin (logCount cK A.card) × Fin (numParts A.card δ) → ℕ → (ℕ → ℕ) → Ω → ℕ → Option ℕ)
        (η : ℝ), 0 ≤ η → InverterLaw μ build η →
        unifAvg ((passingAttempts A B R δ (logCount cK A.card) (numParts A.card δ)).filter
              fun x => CleanFor B R x.1 c)
            (fun x => μ.real {ω |
              recoverOutput B R (toRun x) (runInverters B R build (toRun x) ω)
                  (numParts A.card δ) (residue x.1 c) ≠
                unmarkedClass A B R x.1 (residue x.1 c)}) ≤
          C / Real.log A.card + (logCount cK A.card : ℝ) * (numParts A.card δ : ℝ) * η := by sorry

end RecoveryStorage3SUM.Adaptive
