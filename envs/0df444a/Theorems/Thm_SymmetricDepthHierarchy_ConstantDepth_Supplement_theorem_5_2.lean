-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_5_2
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:03:15.61359+00:00
-- url     : https://prove2.me/theorems/bdd7f9a8-4a53-4a3e-92bc-b525924a97a6
-- title:
--   Theorem 5.2 — symVBP is contained in symVAC¹
-- statement:
--   Let K be any characteristic-zero field. The symmetric classes use polynomial orbit bounds under all extending automorphisms, with no degree or total-size bound; the positive depth exponent k, where present, is an arbitrary integer at least one. Strict inclusion includes both containment and a separating family.
--
--   $$
--   \mathrm{symVBP}\subseteq\mathrm{symVAC}^1.
--   $$
--
--   This is a companion theorem; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 13 (PDF p. 16), Theorem 5.2; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Branching

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem theorem_5_2 (K : Type) [Field K] [CharZero K] : symVBP K ⊆ symVACK K 1 := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
