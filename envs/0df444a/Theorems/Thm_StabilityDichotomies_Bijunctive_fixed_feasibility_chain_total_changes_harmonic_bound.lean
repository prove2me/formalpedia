-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_fixed_feasibility_chain_total_changes_harmonic_bound
-- name    : StabilityDichotomies.Bijunctive.fixed_feasibility_chain_total_changes_harmonic_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:10:03.412077+00:00
-- url     : https://prove2.me/theorems/4ec597ad-2691-4c30-a04e-56c4b44cfbd1
-- title:
--   Total feasibility-chain changes have the harmonic source bound
-- statement:
--   For a satisfiable input, a fixed graph subinstance, and any fixed increasing chain of feasibility subinstances lying between the graph and the input, the sum over chain steps and variables of output-bit change probabilities under independent exponential shifts is at most $r_\Gamma |\mathcal C| H_{2|V|}$, where $r_\Gamma$ is maximum relation arity. Isolated variables contribute zero. This is a fixed-chain version of equation (8).
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step, equation (8).

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.fixed_feasibility_chain_total_changes_harmonic_bound {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I G : Instance Γ V) (hI : Satisfiable I)
    (F : ℕ → Instance Γ V) (k : ℕ)
    (hG : ∀ c ∈ G.constraints, c ∈ (F 0).constraints)
    (hbase : ∀ i ≤ k, ∀ c ∈ (F 0).constraints, c ∈ (F i).constraints)
    (hIcontains : ∀ i ≤ k, ∀ c ∈ (F i).constraints, c ∈ I.constraints)
    (hchain : ∀ i < k, ∀ c ∈ (F i).constraints, c ∈ (F (i+1)).constraints)
    (β : ℝ) (hβ : 0 < β) :
    (∑ i ∈ Finset.range k, ∑ v : V,
      (Measure.pi (fun _ : Literal V => expMeasure β)
        {δ : Literal V → ℝ |
          decide (literalScore rep G (F i) δ (v,false) < literalScore rep G (F i) δ (v,true)) ≠
          decide (literalScore rep G (F (i+1)) δ (v,false) < literalScore rep G (F (i+1)) δ (v,true))}).toReal) ≤
      (maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ) := by
  sorry
