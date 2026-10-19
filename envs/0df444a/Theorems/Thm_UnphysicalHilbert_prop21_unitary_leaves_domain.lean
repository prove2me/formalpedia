-- Prove2me | Theorems.Thm_UnphysicalHilbert_prop21_unitary_leaves_domain
-- name    : UnphysicalHilbert.prop21_unitary_leaves_domain
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:07:02.656664+00:00
-- url     : https://prove2.me/theorems/655eea9e-df88-40c6-9e68-3dd1596b14fc
-- title:
--   Proposition 21 — unitaries can move states out of the domain of an unbounded operator
-- statement:
--   Let $H$ and $Y$ be complex Hilbert spaces and $X:D(X)\subseteq H\to Y$ a closed, unbounded linear operator (as in Proposition 20). Then there exist a unitary operator $U:H\to H$ and a vector $x\in D(X)$ such that
--   $$Ux\notin D(X).$$
--
--   Unitary transformations, which are the isomorphisms of Hilbert spaces, do not in general preserve the set of states on which a given unbounded observable is defined.
--
--   **Formalization Note** "In general" is formalized as existence of such a unitary for every closed unbounded $X$. Unitaries are linear isometric equivalences $H\to H$.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Section VI, p. 11, Proposition 21

import Mathlib

namespace UnphysicalHilbert

/-- Proposition 21: a unitary operator can move vectors out of the domain of an unbounded
closed operator. -/
theorem prop21_unitary_leaves_domain
    {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (X : H →ₗ.[ℂ] Y) (hX : X.IsClosed)
    (hunb : ¬ ∃ C : ℝ, ∀ x : X.domain, ‖X x‖ ≤ C * ‖(x : H)‖) :
    ∃ U : H ≃ₗᵢ[ℂ] H, ∃ x ∈ X.domain, U x ∉ X.domain := by
  sorry

end UnphysicalHilbert
