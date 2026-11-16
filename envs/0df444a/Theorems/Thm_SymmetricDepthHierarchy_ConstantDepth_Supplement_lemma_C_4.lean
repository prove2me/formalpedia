-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_C_4
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:11:36.275766+00:00
-- url     : https://prove2.me/theorems/4a095626-00c9-4c5a-b345-bfb317e27ed0
-- title:
--   Lemma C.4 — Forestwidth and root-path vertex budget
-- statement:
--   Let K,Delta,q>=1 be integers and F any finite simple graph. The symbol T_q^K denotes the distinct-vertex root-path budget, and fw is the published empty-root forestwidth. Both implications are asserted.
--
--   $$
--   \operatorname{fw}_\Delta(F)\le K-1\Rightarrow F\in\mathcal T_{\Delta K}^K,\qquad F\in\mathcal T_q^K\Rightarrow\operatorname{fw}_q(F)\le K-1.
--   $$
--
--   This result supports Theorem C.10; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
--   - encoding: distinct vertices in the union of bags on each root-leaf path → the same union bound on every root-to-node path; reason: every node of a finite rooted tree extends to a leaf, so the two bounds are equivalent
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 44 (PDF p. 47), Lemma C.4; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Paths

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem lemma_C_4 (K Δ q : ℕ) (hK : 1 ≤ K) (hΔ : 1 ≤ Δ) (hq : 1 ≤ q)
    (F : FinGraph) :
    (FWLe F.G Δ (K-1) → inT F.G K (Δ*K)) ∧
    (inT F.G K q → FWLe F.G q (K-1)) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
