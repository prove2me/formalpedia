-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_corollary_4_11
-- name    : RecoveryStorage3SUM.Adaptive.corollary_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:05.543023+00:00
-- url     : https://prove2.me/theorems/c25203fa-185e-4000-90d9-8af1bf1c50b4
-- title:
--   Corollary 4.11 — simultaneously for all targets, some run is clean and complete
-- statement:
--   Let $A,B$ be sets of $n$ polynomially bounded integers, $0\le\delta<1$, $d>0$, and $R$ a sample passing the coverage check. Take $J=\lceil c_J\log n\rceil$, $K=\lceil c_K\log n\rceil$ with $c_K$ large and $c_J\ge1$, and inverters each correct except with probability $\eta$. For large $n$, over $J$ accepted runs and the inverter coins, except with probability $n^{-d}+JKL\eta$,
--   $$\forall c\ \text{polynomially bounded}\ \ \exists j:\quad \text{run }j\text{ is clean for }c\text{ and }\mathrm{Recover}_j(c\bmod p_j)=M_{c\bmod p_j}.$$
--
--   This event is chosen before any query, which is what makes the data structure safe against adaptive queries.
--
--   Differences from the source:
--   - generalization: randomness of the FN structures of Lemma 2.3 → any probability space with failure at most $\eta$ per structure, adding a term $\eta$ per structure to the bound; reason: the coins of Lemma 2.3 are an instance, with $\eta$ polynomially small, which gives the sources "w.h.p."
--   - reading: "with high probability" → for every fixed exponent $d>0$, failure at most $n^{-d}$ for $n\ge n_0$; reason: pp.10-13 give tunable polynomial tails
--   - reading: "the run", redrawn on a failed load check → uniform on attempts passing the load check, independent across runs given $R$; reason: this is exactly the conditional law of an accepted attempt; exhausting the attempts is the separate failure of line 7
--   - reading: "after a successful preprocessing every unmarked value is light" → fixed sample $R$ passing the coverage check of Algorithm 1; reason: that check runs before any run is drawn (line 2); its failure is bounded by Lemma 4.1
--   - encoding: integers bounded by $n^{O(1)}$ (standing assumption, §2) → $|x|\le H(n+2)^\kappa$ with $H,\kappa$ fixed first; reason: same class of inputs; constants are chosen after them
--   - encoding: real sizes $L=6n^\delta\log^2 n$, $|R|=3n^{1-\delta}$, prime range from $n^{2-\delta}\log^3 n$, "$L$ divides $n$" → $L=\lceil6n^\delta\log^2n\rceil$, $|R|=\min(\lceil3n^{1-\delta}\rceil,n)$, primes in $[P,2P)$ with $P=\lceil n^{2-\delta}\log^3n\rceil$, and parts of sizes $\lfloor n/L\rfloor$ or $\lceil n/L\rceil$; reason: integer rounding preserves the asymptotic bounds and isolation constants; it is exact on the integral simplifying regime; the sample cap is inactive for positive delta at large n and gives R=A at the otherwise undefined delta=0 sampler
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Corollary 4.11, p.13

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Laws

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

open MeasureTheory in
/-- Corollary 4.11, p.13: on a sample `R` that passed the coverage check, except with probability
`n^{-d} + JKLη` over `J` accepted runs and the inverter coins, **for every** possible target `c` some run
is clean for `c` and its `Recover(r)` outputs all of `M_r`, `r = c mod p`. -/
theorem corollary_4_11 (H κ : ℕ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (d : ℝ) (hd : 0 < d) :
    ∃ cK₀ : ℕ, ∀ cK cJ : ℕ, cK₀ ≤ cK → 1 ≤ cJ → ∃ n₀ : ℕ, ∀ A B R : Finset ℤ,
      n₀ ≤ A.card → B.card = A.card →
      (∀ a ∈ A, PolyBounded H κ A.card a) → (∀ b ∈ B, PolyBounded H κ A.card b) →
      R ∈ sampleSpace A δ → HeavyCovered A B R δ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (build : Fin (logCount cJ A.card) × (Fin (logCount cK A.card) × Fin (numParts A.card δ)) →
          ℕ → (ℕ → ℕ) → Ω → ℕ → Option ℕ)
        (η : ℝ), 0 ≤ η → InverterLaw μ build η →
        unifAvg (acceptedRuns A B R δ (logCount cJ A.card) (logCount cK A.card) (numParts A.card δ))
            (fun runs => μ.real {ω | ¬ ∀ c : ℤ, PolyBounded H κ A.card c →
              ∃ j, CleanFor B R (runs j).1 c ∧
                recoverOutput B R (toRun (runs j))
                    (runInverters B R (fun kl => build (j, kl)) (toRun (runs j)) ω)
                    (numParts A.card δ) (residue (runs j).1 c) =
                  unmarkedClass A B R (runs j).1 (residue (runs j).1 c)}) ≤
          (A.card : ℝ) ^ (-d) +
            (logCount cJ A.card : ℝ) * (logCount cK A.card : ℝ) * (numParts A.card δ : ℝ) * η := by sorry

end RecoveryStorage3SUM.Adaptive
