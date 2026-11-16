-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_theorem_4_6
-- name    : SingleSampleCombPI.XOS.Supplement.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:44:23.916833+00:00
-- url     : https://prove2.me/theorems/80b2c420-6ac4-4140-a0d0-9e0db42b828a
-- title:
--   Theorem 4.6 — Full continuous greedy ratios and efficient concave implementation
-- statement:
--   For all continuous capped-XOS buyers, exact Algorithm 5 is $637/1250=0.5096$-competitive in random order and has the entire smooth guarantee $\Gamma(q)=q-q^2/2$ for $q\in[0,1]$. Concavity is not required for these two conclusions.
--
--   Separately, under concavity and the source value, supergradient and supporting-price oracle access, there exists a finite real-oracle program implementing the greedy step up to the source accuracy. One program and positive uniform polynomial constants work for all sizes, profiles, orders and $\epsilon>0$. Every execution halts, all queries respect their domains, and total primitive operations, value queries, supergradient queries and supporting-price queries are separately polynomial in $n,m,\log(1/\epsilon)$. The resulting approximate Algorithm 5 has ratio at least $0.5096-\epsilon$ and smooth ratios at least $q-q^2/2-\epsilon$ on the whole interval. Negative lower bounds are harmlessly truncated at zero.
--
--   Differences from the source:
--   - encoding: cube valuations with one-sided supporting prices → published Buyer/Regime interfaces evaluated on their allocation domains; reason: Valid contains exactly normalization, nonnegativity, monotonicity and one-sided support; the demand field is unused in noncomputational continuous statements
--   - encoding: continuous capped-XOS class → ContinuousBuyer: a continuous valuation with the source one-sided supporting-price interface; reason: Proposition 2.1 identifies these classes on the whole cube; no concavity or finite-clause-family restriction is included in the exact guarantees
--   - encoding: an implementation in poly(n,m,log(1/ε)) time and value, supergradient and supporting queries → existence of a finite real-oracle program with halting/safety conclusions and separately counted executions bounded by uniform polynomials; reason: programs have only specified arithmetic/memory/oracle instructions; cost and accuracy are conclusions, not algorithm certificates; source efficiency is existential and no optimizer proof is requested in this statement-only pass
--   - encoding: arbitrary ε>0 and a sufficiently large universal approximation constant → precision 1+ceil(max(0,log(1/ε))), target min(ε,1/2) Mᵢ/[C(n+1)²], uniform positive integers before instances, and nonnegative truncation of lower ratios; reason: this handles n=0, the zero Mᵢ case and large ε without narrowing inputs; the step tolerance is at least as accurate as the source needs and changing the polynomial or constant does not change its complexity class
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem 4.6, printed p. 20 / PDF p. 22; proof printed 21–24 / PDF 23–26.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Oracle

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Theorem 4.6, PDF 22 / printed 20. Exact continuous greedy, both
ratios, and existence of a uniform terminating real-oracle implementation.
No runtime certificate or accuracy guarantee is assumed of its program. -/
theorem theorem_4_6 :
    (∀ n m : ℕ, (alg5 n m).FDCompetitive ContinuousBuyer (637/1250) ∧
      (alg5 n m).Smooth ContinuousBuyer (fun q => q-q^2/2)) ∧
    ∃ (P : RProgram) (K C B : ℕ), 0 < K ∧ 0 < C ∧ 0 < B ∧ ApproxImplementation P K C ∧
      ∀ n m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ g : Buyer m → Vec m → Vec m,
        (∀ b, ConcaveBuyer b → SupergradientOracle b (g b)) →
        (∀ ρ v, (∀ i, ConcaveBuyer (v i)) →
          QCost.Bounded (approxRunCost P K ε n m g ρ v) B (n+m+precision ε)) ∧
        (approx5 P K ε n m g).FDCompetitive ConcaveBuyer (max 0 (637/1250-ε)) ∧
        (approx5 P K ε n m g).Smooth ConcaveBuyer (fun q => max 0 (q-q^2/2-ε)) := by sorry

end SingleSampleCombPI.XOS.Supplement
