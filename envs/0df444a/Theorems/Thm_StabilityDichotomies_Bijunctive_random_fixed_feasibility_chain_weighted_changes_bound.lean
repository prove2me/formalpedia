-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_random_fixed_feasibility_chain_weighted_changes_bound
-- name    : StabilityDichotomies.Bijunctive.random_fixed_feasibility_chain_weighted_changes_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:14:12.204928+00:00
-- url     : https://prove2.me/theorems/d1d29470-7e5f-4d5f-a9f0-e57f2fd5c320
-- title:
--   Shift-independent random feasibility chains have harmonic total change
-- statement:
--   Fix a satisfiable instance and graph. Randomize over a finite family of increasing feasibility chains using any shift-independent probability weights. For each chain step allow any coefficient between zero and one, including the cutoff-rank coefficient j/(k+1) used in the source. The weighted expected total of all bit changes remains bounded by the nonisolated-variable upper bound times the harmonic number of the number of literals.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, equation (8) and the following outside-first-subinstance cutoff average.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.random_fixed_feasibility_chain_weighted_changes_bound
    {Γ : Language} {V J : Type} [Fintype V] [Fintype J]
    (rep : TwoCNFRepresentation Γ) (I G : Instance Γ V) (hI : Satisfiable I)
    (F : J → ℕ → Instance Γ V) (k : J → ℕ)
    (hG : ∀ j c, c ∈ G.constraints → c ∈ (F j 0).constraints)
    (hbase : ∀ j i, i ≤ k j → ∀ c ∈ (F j 0).constraints, c ∈ (F j i).constraints)
    (hIcontains : ∀ j i, i ≤ k j → ∀ c ∈ (F j i).constraints, c ∈ I.constraints)
    (hchain : ∀ j i, i < k j → ∀ c ∈ (F j i).constraints, c ∈ (F j (i+1)).constraints)
    (β : ℝ) (hβ : 0 < β) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp_sum : ∑ j, p j = 1) (a : J → ℕ → ℝ)
    (_ha0 : ∀ j i, 0 ≤ a j i) (ha1 : ∀ j i, a j i ≤ 1) :
    (∑ j, p j * ∑ i ∈ Finset.range (k j), a j i * ∑ v : V,
      (Measure.pi (fun _ : Literal V => expMeasure β)
        {δ : Literal V → ℝ |
          decide (literalScore rep G (F j i) δ (v,false) < literalScore rep G (F j i) δ (v,true)) ≠
          decide (literalScore rep G (F j (i+1)) δ (v,false) < literalScore rep G (F j (i+1)) δ (v,true))}).toReal) ≤
      (maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ) := by
  sorry
