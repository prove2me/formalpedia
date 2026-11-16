-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_theorem_4_2
-- name    : SingleSampleCombPI.XOS.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:41:43.700301+00:00
-- url     : https://prove2.me/theorems/a811d8bd-6959-47cb-89cf-da95297edeb5
-- title:
--   Theorem 4.2 — Unconditional 1/2 barrier for randomized adversarial-order XOS free-disposal allocation
-- statement:
--   Fix any $\epsilon>0$ and any family of randomized online free-disposal algorithms, one for every finite number of buyers and indivisible items. There are positive finite sizes, normalized monotone XOS buyer valuations, valid supporting-price and demand maps, and an arrival order fixed before the algorithm’s random choices, for which
--   $$\mathbb E[\mathrm{FD}(\mathrm{Alg}(v))]<(\tfrac12+\epsilon)\mathrm{Opt}(v).$$
--   The family has unrestricted state, computation, query access to revealed buyer types and probability spaces of internal random seeds. This is a barrier to a uniform ratio above one half across finite sizes, not a statement that every fixed size has that barrier.
--
--   Differences from the source:
--   - encoding: no randomized online algorithm achieves a uniform ratio 1/2+ε, regardless of computation → for every family F n m of published randomized FD state machines there are finite positive sizes and a fixed XOS profile and fixed order with expected FD strictly below (1/2+ε)Opt; reason: the finite sizes, profile and order are chosen outside the seed integral; no operation, query, state-size or seed-cardinality bound is imposed
--   - encoding: valuations and one-sided supporting-price maps on the source allocation domains → published Buyer, Regime and cube interfaces with real-valued functions evaluated only on the allocation domain; reason: the stored demand field is unused in noncomputational continuous statements; no support, continuity or concavity condition is added to the source valuation class
--   - encoding: expectations over random seeds, uniform permutations and independent GoG assignments → published nonnegative lower expectations in ENNReal with explicit finite averages and arbitrary probability spaces of internal seeds; reason: for measurable source payoffs these are the ordinary expectations; no finite-support or atomless-input restriction is introduced
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem 4.2, printed p. 18 / PDF p. 20; proof printed 40–42 / PDF 42–44.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Online

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Theorem 4.2, printed p. 18 / PDF p. 20. The adversary chooses the
profile and order before the random seed. Sizes may depend on the algorithm
family and epsilon. There is no restriction on computation, queries, state,
or the cardinality or atomicity of the probability space of random seeds. -/
theorem theorem_4_2 (ε : ℝ) (hε : 0 < ε)
    (F : (n m : ℕ) → FDAlg .indivisible n m) :
    ∃ (n m : ℕ) (v : Fin n → Buyer m) (ρ : Equiv.Perm (Fin n)),
      0 < n ∧ 0 < m ∧ (∀ i, XOSBuyer (v i)) ∧
      pexp (F n m).seed (fun ω => ENNReal.ofReal
        (FD .indivisible v (fdRun (F n m) ω ρ v))) <
        ENNReal.ofReal (1 / 2 + ε) * ENNReal.ofReal (Opt .indivisible v) := by sorry

end SingleSampleCombPI.XOS.Supplement
