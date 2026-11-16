-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_5_7
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:06:40.268896+00:00
-- url     : https://prove2.me/theorems/bd306170-7d7e-43ac-8f4a-de9ffaa9c797
-- title:
--   Theorem 5.7 — Strict hierarchy at every positive integer exponent
-- statement:
--   Let K be any characteristic-zero field. The symmetric classes use polynomial orbit bounds under all extending automorphisms, with no degree or total-size bound; the positive depth exponent k, where present, is an arbitrary integer at least one. Strict inclusion includes both containment and a separating family.
--
--   $$
--   \forall k\ge1,\quad\mathrm{symVAC}^k\subsetneq\mathrm{symVAC}^{k+1}.
--   $$
--
--   This is a companion theorem; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 14 (PDF p. 17), Theorem 5.7; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem theorem_5_7 (K : Type) [Field K] [CharZero K] (k : ℕ) (hk : 1 ≤ k) :
    symVACK K k ⊂ symVACK K (k+1) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
