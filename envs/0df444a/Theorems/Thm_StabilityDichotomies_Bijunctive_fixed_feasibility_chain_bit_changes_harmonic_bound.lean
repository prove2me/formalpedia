-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_fixed_feasibility_chain_bit_changes_harmonic_bound
-- name    : StabilityDichotomies.Bijunctive.fixed_feasibility_chain_bit_changes_harmonic_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:07:42.948206+00:00
-- url     : https://prove2.me/theorems/cd4e39d3-3753-4f3a-b721-c83be1ff1536
-- title:
--   Feasible-root changes along any fixed chain have harmonic expected count
-- statement:
--   Fix a satisfiable original instance, a graph subinstance, a variable, and any fixed increasing chain of feasibility subinstances that starts above the graph and remains within the original instance. Under independent rate-$\beta>0$ exponential shifts, the sum of probabilities that the variable’s output bit changes between consecutive feasibility subinstances is at most $H_{2|V|}$. This is the per-variable form of the paper’s equation (8), for a fixed chain.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step, equation (8).

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.fixed_feasibility_chain_bit_changes_harmonic_bound {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I G : Instance Γ V) (hI : Satisfiable I)
    (F : ℕ → Instance Γ V) (k : ℕ) (v : V)
    (hG : ∀ c ∈ G.constraints, c ∈ (F 0).constraints)
    (hbase : ∀ i ≤ k, ∀ c ∈ (F 0).constraints, c ∈ (F i).constraints)
    (hIcontains : ∀ i ≤ k, ∀ c ∈ (F i).constraints, c ∈ I.constraints)
    (hchain : ∀ i < k, ∀ c ∈ (F i).constraints, c ∈ (F (i+1)).constraints)
    (β : ℝ) (hβ : 0 < β) :
    (∑ i ∈ Finset.range k,
      (Measure.pi (fun _ : Literal V => expMeasure β)
        {δ : Literal V → ℝ |
          decide (literalScore rep G (F i) δ (v,false) < literalScore rep G (F i) δ (v,true)) ≠
          decide (literalScore rep G (F (i+1)) δ (v,false) < literalScore rep G (F (i+1)) δ (v,true))}).toReal) ≤
      (harmonic (Fintype.card (Literal V)) : ℝ) := by
  sorry
