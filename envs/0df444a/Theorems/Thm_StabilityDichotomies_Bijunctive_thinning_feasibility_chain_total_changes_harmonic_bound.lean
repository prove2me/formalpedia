-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_thinning_feasibility_chain_total_changes_harmonic_bound
-- name    : StabilityDichotomies.Bijunctive.thinning_feasibility_chain_total_changes_harmonic_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:01:24.461901+00:00
-- url     : https://prove2.me/theorems/916f6ac0-45fa-4f8c-b075-b3172438ae5d
-- title:
--   Increasing occurrence-mask feasibility chains obey the harmonic change bound
-- statement:
--   Fix any first-stage occurrence mask and any increasing chain of occurrence masks extending it. With its implication graph fixed and iid exponential shifts, the sum over chain steps and variables of the feasible-root output-change probabilities is at most $r_\Gamma |C|H_{2|V|}$. This specializes equation (8) to the actual occurrence-mask representation used by the algorithm.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, equation (8).

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.thinning_feasibility_chain_total_changes_harmonic_bound {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (m : ℕ → Fin I.constraints.card → Bool) (k : ℕ)
    (hbase : ∀ i ≤ k, ∀ j, m 0 j = true → m i j = true)
    (hchain : ∀ i < k, ∀ j, m i j = true → m (i+1) j = true)
    (β : ℝ) (hβ : 0 < β) :
    (∑ i ∈ Finset.range k, ∑ v : V,
      (Measure.pi (fun _ : Literal V => expMeasure β)
        {δ : Literal V → ℝ |
          decide (literalScore rep (thinnedInstance I (m 0)) (thinnedInstance I (m i)) δ (v,false) <
            literalScore rep (thinnedInstance I (m 0)) (thinnedInstance I (m i)) δ (v,true)) ≠
          decide (literalScore rep (thinnedInstance I (m 0)) (thinnedInstance I (m (i+1))) δ (v,false) <
            literalScore rep (thinnedInstance I (m 0)) (thinnedInstance I (m (i+1))) δ (v,true))}).toReal) ≤
      (maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ) := by
  sorry
