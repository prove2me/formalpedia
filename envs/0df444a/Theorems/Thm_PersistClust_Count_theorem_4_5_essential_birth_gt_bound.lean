-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_essential_birth_gt_bound
-- name    : PersistClust.Count.theorem_4_5_essential_birth_gt_bound
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T17:09:19.888332+00:00
-- url     : https://prove2.me/theorems/652b6c32-8688-424f-a910-1dda7f9c2b6d
-- title:
--   Theorem 4.5 support - separated diagrams: no essential bar is born below the separation band
-- statement:
--   Let f be a real-valued function on a metric space X and let diagram0 f be its sublevel-set persistence diagram. If diagram0 f is (d1, d2)-separated and Delta < d2, then there is no essential bar (a nonzero diagram point whose death coordinate is bottom) whose birth coordinate is at most Delta. Equivalently: every essential bar of a (d1, d2)-separated diagram is born strictly above d2. The proof first shows the underlying bound - an essential bar cannot lie in the DeltaN d1 region (that would force a death coordinate strictly below bottom), so it lies in the LamE d2 region, giving d2 < birth - and then combines it with the assumed birth bound to get d2 < Delta < d2, a contradiction. This is the terminal step of the elder chase: an essential bar born at or below tau + c*delta contradicts separation whenever tau + c*delta < d2.
-- source:
--   The chase-final terminal step of the L_tau cluster in the proof of Theorem 4.5, Persistence-Based Clustering in Riemannian Manifolds (rr/6968). Child of theorem_4_5 (id 8476e8c8-3232-437b-939f-4ea37c366d80); direct companion of the accepted theorem_4_5_elder_chase_essential_bar (id 9cfba490-b1d0-4057-9d74-80806c1fc1df), whose output this bound refutes; sibling of the accepted theorem_4_5_gamma_degenerate and theorem_4_5_interleaving_corrected. The essential-birth lower bound also appears in the auxiliary layer of the accepted theorem_4_8_core solution.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count

namespace PersistClust.Count

theorem theorem_4_5_essential_birth_gt_bound {X : Type*} [MetricSpace X] {f : X → ℝ} {d₁ d₂ : ℝ} (hsep : IsSeparated (diagram0 f) d₁ d₂) {Δ : ℝ} (hΔd : Δ < d₂)
    {b : EReal} (hb : diagram0 f (b, ⊥) ≠ 0) (hble : b ≤ (((Δ : ℝ) : ℝ) : EReal)) :
    False
    := by sorry
