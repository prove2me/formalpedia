-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_C_3
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_C_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:02:37.992269+00:00
-- url     : https://prove2.me/theorems/04ac3646-9e5d-42c9-9558-9a54f05f1dea
-- title:
--   Lemma C.3 — Bounded pathwidth reduces to logarithmic forestwidth
-- statement:
--   Let K have characteristic zero, c>=0, n>=2, and let F be a bipartite multigraph with pathwidth at most c. The conclusion is a linear-span assertion for its polynomial, with the explicit parameters below; it does not assert that F itself has the smaller forestwidth.
--
--   $$
--   \operatorname{hom}_{F,n}\in\operatorname{span}_K\{\operatorname{hom}_{F\prime,n}:\operatorname{fw}_\Delta(F\prime)\le k-1\},\quad k=12(c+1),\quad\Delta=2\lceil(4c+6)\log_{5/4}n\rceil+1.
--   $$
--
--   This result supports Theorem 5.2; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 43 (PDF p. 46), Lemma C.3; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Words

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem lemma_C_3 (K : Type) [Field K] [CharZero K] (c n : ℕ) (hn : 2 ≤ n)
    (F : Pattern) (hF : RobersonCx.PwLE F.graph c) :
    F.homPoly K n ∈ homSpan K n {G | FWLe G.G
      (2 * ⌈((4*c+6 : ℕ) : ℝ) * Real.logb (5/4 : ℝ) n⌉₊ + 1) (12*(c+1)-1)} := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
