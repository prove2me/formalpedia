-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_proposition_7_5
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.proposition_7_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T11:09:55.0055+00:00
-- url     : https://prove2.me/theorems/6c17602b-e80f-49a8-9b52-038d449e4d96
-- title:
--   Proposition 7.5 — The permanent belongs to symVNP over any field
-- statement:
--   Let K be any field, including positive characteristic. The permanent family in the square matrix variables satisfies Definition 7.1, with the full joint-action and Boolean-sum witness conditions.
--
--   $$
--   (\operatorname{perm}_n)\in\mathrm{symVNP}.
--   $$
--
--   This result supports Theorem 7.7; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 19 (PDF p. 22), Proposition 7.5; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Joint

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem proposition_7_5 (K : Type) [Field K] : permanentFamily K ∈ symVNP K := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
