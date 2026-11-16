-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_C_2
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:02:08.565802+00:00
-- url     : https://prove2.me/theorems/1ebc5631-46f3-4d22-bafe-2b73a58bbf16
-- title:
--   Lemma C.2 — Atomic-word encoding and pathwidth bounds
-- statement:
--   Let K have characteristic zero, c>=0, n>=1, and let u be any finite word of atomic edge and reset graphs. All displayed identities and both pathwidth bounds hold. In addition, both F_u and F_u^circle have at most 2(c+1)+|u| vertices. Conversely every pattern F of pathwidth at most c has such a word with F_u isomorphic to the disjoint union of F and exactly 2(c+1) isolated vertices, c+1 on each side. The empty word is included.
--
--   $$
--   (F_u)_n=\prod_i(u_i)_n,\quad\mathbf1^T(F_u)_n\mathbf1=\operatorname{hom}_{F_u,n},\quad\operatorname{tr}((F_u)_n)=\operatorname{hom}_{F_u^\circ,n},\quad\operatorname{pw}(F_u)\le2c+1,\quad\operatorname{pw}(F_u^\circ)\le4c+3.
--   $$
--
--   This result supports Theorem 5.2; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 42 (PDF p. 45), Lemma C.2; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Words

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem lemma_C_2 (K : Type) [Field K] [CharZero K] (c n : ℕ) (hn : 1 ≤ n) :
    (∀ u : List (Atom c),
      (wordBi u).matrix K n = ((u.map fun a => (atomBi a).matrix K n).prod) ∧
      (∑ a, ∑ b, (wordBi u).matrix K n a b) = (wordBi u).pattern.homPoly K n ∧
      Matrix.trace ((wordBi u).matrix K n) = (wordBi u).close.homPoly K n ∧
      (wordBi u).pattern.numVertices ≤ 2*(c+1) + u.length ∧
      (wordBi u).close.numVertices ≤ 2*(c+1) + u.length ∧
      RobersonCx.PwLE (wordBi u).pattern.graph (2*c+1) ∧
      RobersonCx.PwLE (wordBi u).close.graph (4*c+3)) ∧
    (∀ F : Pattern, RobersonCx.PwLE F.graph c →
      ∃ u : List (Atom c), patternIso (wordBi u).pattern (withIsolates F c)) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
