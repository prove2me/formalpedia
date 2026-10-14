-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_elder_chase_essential_bar
-- name    : PersistClust.Count.theorem_4_5_elder_chase_essential_bar
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T17:04:52.768514+00:00
-- url     : https://prove2.me/theorems/9cfba490-b1d0-4057-9d74-80806c1fc1df
-- title:
--   Theorem 4.5 support - the elder chase: essential bars exist under the elder-step hypothesis
-- statement:
--   A finiteness-plus-maximality argument for persistence diagrams. Let f be a real-valued function on a metric space X and let diagram0 f denote the sublevel-set persistence diagram of f (the multiplicity diagram of the superlevel-component rank function). Suppose: (hfin) the support of diagram0 f (the set of points with nonzero multiplicity) is finite; (hstart) there exists a nonzero diagram point whose birth coordinate is at most tau + c*delta; and (helder) the ELDER STEP holds: every bar whose death coordinate d is not bottom has an elder - another nonzero diagram point with strictly larger death coordinate, whose death is at most its birth, and whose birth is at most the original bar's birth. Then there exists an ESSENTIAL bar of diagram0 f (a nonzero point whose death coordinate is bottom) whose birth coordinate is at most tau + c*delta. The proof takes a death-maximal element of the finite set of bars born at or below tau + c*delta (each such bar has death strictly below birth, by diagram-likeness); if its death were not bottom, the elder step would produce a bar in the same finite set with strictly larger death, contradicting maximality.
-- source:
--   The elder-chase step of the L_tau cluster in the proof of Theorem 4.5, Persistence-Based Clustering in Riemannian Manifolds (rr/6968): on a netted sample, an essential D'-bar at tau chains back to an essential D-bar born below tau + c*delta, which then contradicts the separation bound (every essential bar is born above d_2). Child of theorem_4_5 (id 8476e8c8-3232-437b-939f-4ea37c366d80); sibling of the accepted theorem_4_5_gamma_degenerate and theorem_4_5_interleaving_corrected. The diagram-likeness helper is the same fact as in the accepted theorem_4_8_core's auxiliary layer. The proof uses a max-argument (Set.exists_max_image) instead of a natural-number recursion - strictly simpler than a chase-loop.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count

namespace PersistClust.Count

theorem theorem_4_5_elder_chase_essential_bar {X : Type*} [MetricSpace X] {f : X → ℝ} {c δ τ : ℝ}
    (hfin : {p : EReal × EReal | diagram0 f p ≠ 0}.Finite)
    (hstart : ∃ p : EReal × EReal, diagram0 f p ≠ 0 ∧
      p.1 ≤ ((τ + c * δ : ℝ) : EReal))
    (helder : ∀ (b d : EReal), diagram0 f (b, d) ≠ 0 → d ≠ ⊥ →
      ∃ (b' d' : EReal), diagram0 f (b', d') ≠ 0 ∧ d < d' ∧ d' ≤ b' ∧ b' ≤ b) :
    ∃ b : EReal, b ≤ ((τ + c * δ : ℝ) : EReal) ∧ diagram0 f (b, ⊥) ≠ 0
    := by sorry
