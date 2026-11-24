-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_7_7
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_7_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T11:10:44.651941+00:00
-- url     : https://prove2.me/theorems/71784861-2930-4072-8883-e4c13c38827e
-- title:
--   Theorem 7.7 — Symmetric completeness of the permanent
-- statement:
--   Let K be any characteristic-zero field. Permanent completeness means membership plus a symmetric permanent projection for every positive component of every symVNP family. Projection matrices have affine entries, independent row and column permutations may witness each symmetry, and their dimension is unbounded.
--
--   $$
--   (\operatorname{perm}_n)\in\mathrm{symVNP},\qquad(\forall(f_n)\in\mathrm{symVNP})(\forall n\ge1)\ f_n\text{ is a symmetric projection of a permanent}.
--   $$
--
--   This is a companion theorem; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 20 (PDF p. 23), Theorem 7.7; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Joint

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem theorem_7_7 (K : Type) [Field K] [CharZero K] :
    permanentFamily K ∈ symVNP K ∧
    ∀ f : Family K, f ∈ symVNP K → ∀ n, 1 ≤ n → symmetricProjection (f n) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
