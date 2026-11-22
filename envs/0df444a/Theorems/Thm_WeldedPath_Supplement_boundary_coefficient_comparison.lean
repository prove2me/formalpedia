-- Prove2me | Theorems.Thm_WeldedPath_Supplement_boundary_coefficient_comparison
-- name    : WeldedPath.Supplement.boundary_coefficient_comparison
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-22T18:12:24.086016+00:00
-- url     : https://prove2.me/theorems/d3e10336-3bdc-4a1a-86f7-dabf939ad89e
-- title:
--   Changing the boundary in the forest coefficient space
-- statement:
--   For a valid abstract forest $H$ with $k$ vertices, form the span of its reference-weighted description amplitudes at a boundary $B$. Enlarge $B$ by a set $R$ disjoint from the weld. Under the stated size hypotheses, every vector in the old span has an approximation in the new span with squared error at most $64k|R|2^{-n}$ times its squared norm. In the reverse direction the squared relative error is at most $128k|R|2^{-n}$.
-- source:
--   Carolan et al., Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, Section 4.3, Lemma 4.10 (explicit-constant boundary adjustment). https://arxiv.org/html/2611.05912v1#S4.SS3

import Definitions.Def_WeldedPath_Supplement_projGood

namespace WeldedPath.Supplement

open Classical

theorem boundary_coefficient_comparison {n l : ℕ} {G : WeldedInstance n}
    (H : AbsForest n) (hH : H.IsValid) (hG : G.IsValid)
    (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n-4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (hsmall : (H.k : ℝ)*(B.card : ℝ)*(4/(2:ℝ)^n) ≤ 1/2)
    (R : Finset ℕ) (hRw : Disjoint R (Vweld n))
    (hloss : (H.k : ℝ)*8*(R.card : ℝ)/(2:ℝ)^n ≤ 1/8) :
    let S := fun (A : Finset ℕ) => Submodule.span ℂ
      {f : Hil (Fin H.k → Label n) | ∃ (sel : Finset (Fin H.k)) (φ₀ : Fin H.k → Label n),
        (Description.mk H sel φ₀).IsValid ∧ f = WithLp.toLp 2 (fun φ : Fin H.k → Label n =>
          ((Real.sqrt (if (∀ s ∈ sel,H.Wfix φ s = H.Wfix φ₀ s) ∧
            (∀ s ∈ sel, ∀ u, H.graph.Reachable s u → u ∉ H.Ctree φ s → (φ u).val ∉ A)
            then H.muRef l G φ else 0)) : ℂ))}
    (∀ f ∈ S B, ∃ g ∈ S (B ∪ R), ‖f-g‖^2 ≤ (8*((H.k:ℝ)*8*(R.card:ℝ)/(2:ℝ)^n))*‖f‖^2) ∧
    (∀ g ∈ S (B ∪ R), ∃ f ∈ S B, ‖g-f‖^2 ≤ (16*((H.k:ℝ)*8*(R.card:ℝ)/(2:ℝ)^n))*‖g‖^2) := by sorry

end WeldedPath.Supplement
