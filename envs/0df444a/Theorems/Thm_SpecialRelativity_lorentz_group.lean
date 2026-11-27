-- Prove2me | Theorems.Thm_SpecialRelativity_lorentz_group
-- name    : SpecialRelativity.lorentz_group
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T01:48:56.351799+00:00
-- url     : https://prove2.me/theorems/da3c1a51-a002-4930-8fae-efa36d2edd1b
-- title:
--   The Lorentz transformations form a group
-- statement:
--   **The Lorentz transformations form a group.**
--
--   Let `A` and `B` be Lorentz transformations ($A^{T}\eta A = \eta$, $B^{T}\eta B = \eta$).
--
--   **Conclusion:** a four-fold conjunction —
--   1. the composite is a Lorentz transformation: $(AB)^{T}\eta\,(AB) = \eta$;
--   2. the identity matrix is a Lorentz transformation;
--   3. the determinant of `A` is a unit: $A$ is invertible (in fact $\det(A)^2 = 1$, since $\det(A)^2 \det(\eta) = \det(\eta)$ and $\det(\eta) = -1 \neq 0$);
--   4. the inverse is a Lorentz transformation: $(A^{-1})^{T}\eta\,A^{-1} = \eta$.
--
--   In words: the Lorentz transformations constitute a group — the group with respect to which, per the source, "the laws of physics are invariant". Composite changes of inertial frame, identity frames and reversed frames are all admissible, and every Lorentz transformation has a Lorentz inverse.
--
--   **Formalization note.** Matrix associativity and the determinant computation from $\det(\eta) = -1$ (nondegeneracy of the Minkowski form) are the only inputs beyond matrix algebra; `IsUnit A.det` is the Mathlib-idiomatic way to carry invertibility of `A`.
-- source:
--   Wikipedia, Special relativity, https://en.wikipedia.org/wiki/Special_relativity (source of the quoted statements, reproduced verbatim in the definition file) ('The laws of physics are invariant with respect to Lorentz transformations'; 'the Lorentz transformation replaces the Galilean transformation'); H. Poincare, Sur la dynamique de l'electron, Rendiconti del Circolo Matematico di Palermo 21 (1906); H. Minkowski, Raum und Zeit, address to the 80th Assembly of German Natural Scientists and Physicians (1908)

import Mathlib
import Definitions.Def_SpecialRelativity

namespace SpecialRelativity

open Matrix

/-- Milestone: the Lorentz transformations form a group.  The composite of two
Lorentz transformations is a Lorentz transformation, the identity is one, every
Lorentz transformation is invertible (its determinant squares to `1` because
the Minkowski form is nondegenerate), and its inverse is again a Lorentz
transformation.  This is the group-theoretic skeleton of the source's "The laws
of physics are invariant with respect to Lorentz transformations". -/
theorem lorentz_group (A B : Matrix (Fin 4) (Fin 4) ℝ) (hA : IsLorentz A) (hB : IsLorentz B) :
    IsLorentz (A * B) ∧ IsLorentz (1 : Matrix (Fin 4) (Fin 4) ℝ) ∧ IsUnit A.det ∧
      IsLorentz A⁻¹ := by
  sorry

end SpecialRelativity
