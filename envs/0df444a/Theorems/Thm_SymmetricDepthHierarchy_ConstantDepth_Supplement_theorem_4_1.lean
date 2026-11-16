-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_4_1
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:58:28.36549+00:00
-- url     : https://prove2.me/theorems/42104433-b5df-4a9c-86fb-f8616b53002e
-- title:
--   Theorem 4.1 — P-family equality of symVP and symVAC¹
-- statement:
--   Let K be any characteristic-zero field and let (p_n) be a p-family in the square matrix variables. Both directions are asserted; matrix invariance is supplied by class membership.
--
--   $$
--   \mathrm{symVP}\cap\{\text{p-families}\}=\mathrm{symVAC}^1\cap\{\text{p-families}\}.
--   $$
--
--   This is a companion theorem; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 12 (PDF p. 15), Theorem 4.1; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem theorem_4_1 (K : Type) [Field K] [CharZero K] (p : Family K)
    (hp : pFamily p) : p ∈ symVP K ↔ p ∈ symVACK K 1 := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
