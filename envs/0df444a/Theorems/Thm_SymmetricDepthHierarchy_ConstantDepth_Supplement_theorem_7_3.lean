-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_7_3
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:08:45.588997+00:00
-- url     : https://prove2.me/theorems/977017c7-bfe0-41d0-a53b-dd3d049ca99a
-- title:
--   Theorem 7.3 — symVNP equals every matrix-symmetric polynomial family
-- statement:
--   Over a characteristic-zero field, G_n is the independently defined space of row/column invariant polynomials. The first assertion concerns every family at every positive index. The second holds for every n>=1 and every individual f in G_n: g has a joint-symmetric formula with exactly 2n^2 Boolean variables and all gate orbits at most 4n^2. The auxiliary action is a group homomorphism; there is no degree or total-size bound.
--
--   $$
--   (f_n)\in\mathrm{symVNP}\iff (\forall n\ge1)\ f_n\in G_n,\qquad f(X)=\sum_{e\in\{0,1\}^{2n^2}}g(X,e),\quad\operatorname{maxOrb}(g)\le4n^2.
--   $$
--
--   This is a companion theorem; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 17 (PDF p. 20), Theorem 7.3; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Joint

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem theorem_7_3 (K : Type) [Field K] [CharZero K] :
    (∀ f : Family K, f ∈ symVNP K ↔ invariantFamily f) ∧
    (∀ n, 1 ≤ n → ∀ f : MvPolynomial (Fin n × Fin n) K, invariant f →
      ∃ ρ : Circuit.Gamma n →* Equiv.Perm (Fin (2*n^2)),
      ∃ m, ∃ C : VariableCircuit K ((Fin n × Fin n) ⊕ Fin (2*n^2)) (Fin m),
        C.wellFormed ∧ C.isFormula ∧ C.symmetric (jointAction ρ) ∧
        booleanSum C.polynomial = f ∧ C.maxOrb (jointAction ρ) ≤ 4*n^2) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
