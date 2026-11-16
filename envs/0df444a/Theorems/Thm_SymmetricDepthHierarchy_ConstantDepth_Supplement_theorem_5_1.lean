-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_5_1
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:01:21.045342+00:00
-- url     : https://prove2.me/theorems/0118f710-a00f-4127-b04d-70f2fe01bbfa
-- title:
--   Theorem 5.1 — symVAC⁰ equals symVF
-- statement:
--   Let K be any characteristic-zero field. The symmetric classes use polynomial orbit bounds under all extending automorphisms, with no degree or total-size bound; the positive depth exponent k, where present, is an arbitrary integer at least one. Strict inclusion includes both containment and a separating family.
--
--   $$
--   \mathrm{symVAC}^0=\mathrm{symVF}.
--   $$
--
--   This is a companion theorem; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 13 (PDF p. 16), Theorem 5.1; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem theorem_5_1 (K : Type) [Field K] [CharZero K] : symVAC0 K = symVF K := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
