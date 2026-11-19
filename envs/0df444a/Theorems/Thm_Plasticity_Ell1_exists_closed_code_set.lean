-- Prove2me | Theorems.Thm_Plasticity_Ell1_exists_closed_code_set
-- name    : Plasticity.Ell1.exists_closed_code_set
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T20:09:08.711742+00:00
-- url     : https://prove2.me/theorems/7be79a39-b4b0-43f2-aa1c-2f5ec3ad9e9a
-- title:
--   Coding a continuous injective image of a closed subset of Baire space by a closed set of nonnegative unit vectors of $\ell_1$
-- statement:
--   Let $Y$ be a metric space, $C\subseteq\mathbb N^{\mathbb N}$ closed, and $\varphi$ continuous on $C$ and bijective from $C$ onto $M\subseteq Y$.
--   There are a closed set $E$ of nonnegative unit vectors of $\ell_1(\mathbb N)$ and a bijection $\lambda\colon E\to M$ with $d(\lambda e,\lambda e')\le\|e-e'\|_1/4$ whenever $\|e-e'\|_1<2$.
-- source:
--   Proof draft 'Three constructions of nonplastic Banach unit balls' (ChatGPT Pro, OpenAI, 18 November 2026), Construction B (representing Borel sets on the sphere); the quarter bound is read off its distance estimate

import Mathlib.Analysis.Normed.Lp.lpSpace

namespace Plasticity
theorem Ell1.exists_closed_code_set {Y : Type*} [MetricSpace Y] (M : Set Y)
    (C : Set (ℕ → ℕ)) (hC : IsClosed C)
    (φ : (ℕ → ℕ) → Y) (hφ : ContinuousOn φ C) (hbij : Set.BijOn φ C M) :
    ∃ E : Set (lp (fun _ : ℕ => ℝ) 1), IsClosed E ∧ (∀ e ∈ E, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j) ∧
      ∃ lab : lp (fun _ : ℕ => ℝ) 1 → Y, Set.BijOn lab E M ∧
        ∀ e ∈ E, ∀ e' ∈ E, ‖e - e'‖ < 2 → dist (lab e) (lab e') ≤ ‖e - e'‖ / 4 := by sorry
end Plasticity
