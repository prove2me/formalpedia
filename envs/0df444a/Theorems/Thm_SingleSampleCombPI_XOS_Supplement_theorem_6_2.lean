-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_theorem_6_2
-- name    : SingleSampleCombPI.XOS.Supplement.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:51:43.005964+00:00
-- url     : https://prove2.me/theorems/644d52f6-1bb8-4e14-93f2-e4c2a6c4ff63
-- title:
--   Theorem 6.2 — Exact divisible capped-XOS SSCombPI and efficient concave epsilon-loss version
-- statement:
--   Algorithms 3/5/8 with $q=1-1/\sqrt3$ give a feasible irrevocable single-sample allocation in the GoG model, for all continuous capped-XOS valuations and every adversarial real arrival order, with exact guarantee
--   $$\mathbb E[\mathrm{Alg}]\ge\frac1{6\sqrt3}\mathbb E[\mathrm{Opt}(r)].$$
--   Under the additional concavity and source oracle assumptions, there is a uniform finite real-oracle implementation of the Algorithm 5 component. The same composition is feasible, has ratio at least $1/(6\sqrt3)-\epsilon$ for every $\epsilon>0$, and runs in polynomial time using polynomially many value, supergradient and supporting-price queries in $n,m,\log(1/\epsilon)$. Separate actual counters include all sample replay and real calls; the exact noncomputable guarantee remains separate from this efficient approximation clause.
--
--   Differences from the source:
--   - encoding: cube valuations with one-sided supporting prices → published Buyer/Regime interfaces evaluated on their allocation domains; reason: Valid contains exactly normalization, nonnegativity, monotonicity and one-sided support; the demand field is unused in noncomputational continuous statements
--   - encoding: continuous capped-XOS buyers → ContinuousBuyer and the published Algorithms 1/2/3 with exact Algorithm 5, Algorithm 8 and qStar; reason: Proposition 2.1 supplies the equivalent supporting interface; the real input order stays adversarial
--   - encoding: an implementation in poly(n,m,log(1/ε)) time and value, supergradient and supporting queries → existence of a finite real-oracle program with halting/safety conclusions and separately counted executions bounded by uniform polynomials; reason: programs have only specified arithmetic/memory/oracle instructions; cost and accuracy are conclusions, not algorithm certificates; source efficiency is existential and no optimizer proof is requested in this statement-only pass
--   - encoding: arbitrary ε>0 and a sufficiently large universal approximation constant → precision 1+ceil(max(0,log(1/ε))), target min(ε,1/2) Mᵢ/[C(n+1)²], uniform positive integers before instances, and nonnegative truncation of lower ratios; reason: this handles n=0, the zero Mᵢ case and large ε without narrowing inputs; the step tolerance is at least as accurate as the source needs and changing the polynomial or constant does not change its complexity class
--   - encoding: expectations over the specified independent random choices → explicit fair finite GoG averages and nonnegative expectations over independent algorithm seeds; reason: these are ordinary expectations for measurable source payoffs; no input distribution or finite-support restriction is imposed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem 6.2, printed p. 33 / PDF p. 35; proof printed 33 / PDF 35.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Oracle

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Theorem 6.2, PDF 35 / printed 33. Exact Algorithms 3/5/8, and
separately a feasible efficient concave implementation with epsilon loss. -/
theorem theorem_6_2 :
    (∀ n m : ℕ,
      (∀ H π ωs ρ s r, (∀ i, ContinuousBuyer (s i)) →
        (∀ i, ContinuousBuyer (r i)) →
        Feasible .divisible (alg3 (alg5 n m) (alg8 n) H π () ωs ρ s r)) ∧
      ∀ V : Fin n → Fin 2 → Buyer m, (∀ i t, ContinuousBuyer (V i t)) → ∀ ρ,
        ENNReal.ofReal (1/(6*Real.sqrt 3)) * optExp1 (A := .divisible) V ≤
          alg3Exp (alg5 n m) (alg8 n) qStar ρ V) ∧
    ∃ (P : RProgram) (K C B : ℕ), 0 < K ∧ 0 < C ∧ 0 < B ∧
      ApproxImplementation P K C ∧
      ∀ n m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ g : Buyer m → Vec m → Vec m,
        (∀ b, ConcaveBuyer b → SupergradientOracle b (g b)) →
        (∀ H π ωs ρ s r, (∀ i, ConcaveBuyer (s i)) → (∀ i, ConcaveBuyer (r i)) →
          Feasible .divisible (alg3 (approx5 P K ε n m g) (alg8 n) H π () ωs ρ s r) ∧
          QCost.Bounded (approx3Cost P K ε n m g H π ωs ρ s r) B (n+m+precision ε)) ∧
        ∀ V : Fin n → Fin 2 → Buyer m, (∀ i t, ConcaveBuyer (V i t)) → ∀ ρ,
          ENNReal.ofReal (max 0 (1/(6*Real.sqrt 3)-ε)) * optExp1 (A := .divisible) V ≤
            alg3Exp (approx5 P K ε n m g) (alg8 n) qStar ρ V := by sorry

end SingleSampleCombPI.XOS.Supplement
