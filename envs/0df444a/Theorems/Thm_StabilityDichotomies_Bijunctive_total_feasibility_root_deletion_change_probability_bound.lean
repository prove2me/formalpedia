-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_total_feasibility_root_deletion_change_probability_bound
-- name    : StabilityDichotomies.Bijunctive.total_feasibility_root_deletion_change_probability_bound
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T10:49:55.763052+00:00
-- url     : https://prove2.me/theorems/ac0bbaeb-a3c4-453e-9883-d352931c6394
-- title:
--   Total feasible-root deletion changes obey the harmonic sensitivity bound
-- statement:
--   For a satisfiable instance and $0<\varepsilon\le1$, couple all deletions by the original Definition 4.8 seed. For each deleted occurrence, hold the implication graph with its arcs removed fixed and compare the original and deleted feasible-root sets. Summing their bit-change probabilities over all occurrence-variable pairs gives at most
--   $$\frac{2}{\varepsilon}r_\Gamma|C|H_{2|V|}.$$
--   This is the complete feasible-root part of the sensitivity analysis in Theorem 4.9; it remains a proof obligation.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, equation (8) and cutoff/order averaging.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.total_feasibility_root_deletion_change_probability_bound {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let μ := bijunctiveSeedMeasure rep I ε
    let G := fun (j : Fin I.constraints.card) (z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j))
    let F := fun z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))
    let Fminus := fun (j : Fin I.constraints.card) (z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1) && decide (i ≠ j))
    let mid := fun j z v => decide (literalScore rep (G j z) (F z) z.2.2 (v,false) < literalScore rep (G j z) (F z) z.2.2 (v,true))
    let last := fun j z v => decide (literalScore rep (G j z) (Fminus j z) z.2.2 (v,false) < literalScore rep (G j z) (Fminus j z) z.2.2 (v,true))
    (∑ j : Fin I.constraints.card, ∑ v : V, (μ {z | mid j z v ≠ last j z v}).toReal) ≤
      (2 / ε) * ((maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)) := by
  sorry
