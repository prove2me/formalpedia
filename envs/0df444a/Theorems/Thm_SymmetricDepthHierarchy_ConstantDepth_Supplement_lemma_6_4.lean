-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_6_4
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_6_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T11:07:03.652288+00:00
-- url     : https://prove2.me/theorems/0a556ad7-fdf3-4300-84e7-b7994dedca04
-- title:
--   Lemma 6.4 — ABPs convert to skew circuits
-- statement:
--   Let K be any characteristic-zero field. The symmetric classes use polynomial orbit bounds under all extending automorphisms, with no degree or total-size bound; the positive depth exponent k, where present, is an arbitrary integer at least one. Strict inclusion includes both containment and a separating family.
--
--   $$
--   \mathrm{symVBP}\subseteq\mathrm{symVS}.
--   $$
--
--   This result supports Theorem 6.3; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 15 (PDF p. 18), Lemma 6.4; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Branching

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem lemma_6_4 (K : Type) [Field K] [CharZero K] : symVBP K ⊆ symVS K := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
