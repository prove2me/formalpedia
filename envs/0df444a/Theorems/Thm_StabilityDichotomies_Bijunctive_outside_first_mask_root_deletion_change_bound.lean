-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_outside_first_mask_root_deletion_change_bound
-- name    : StabilityDichotomies.Bijunctive.outside_first_mask_root_deletion_change_bound
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T10:54:18.065626+00:00
-- url     : https://prove2.me/theorems/6f34fa42-1329-46df-9755-332bbdcef3d2
-- title:
--   Outside-first-mask root changes obey the harmonic bound
-- statement:
--   For deletions whose occurrence lies outside the first-stage mask, the summed feasible-root bit-change probabilities are at most $r_\Gamma|C|H_{2|V|}$. This is the outside-mask cutoff-prefix averaging step in the proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, equation (8) and cutoff/order averaging.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.outside_first_mask_root_deletion_change_bound {Γ : Language} {V : Type} [Fintype V]
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
    (∑ j : Fin I.constraints.card, ∑ v : V, (μ {z | mid j z v ≠ last j z v ∧ ¬ (z.1 j ≤ 1 - ε / 2)}).toReal) ≤
      ((maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)) := by
  sorry
