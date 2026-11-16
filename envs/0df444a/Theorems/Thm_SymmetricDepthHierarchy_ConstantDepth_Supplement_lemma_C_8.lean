-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_C_8
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_C_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:13:32.178479+00:00
-- url     : https://prove2.me/theorems/32860031-8dae-4e26-ac41-1c4bbe0e960d
-- title:
--   Lemma C.8 (corrected: positive dimension in clause 2) — Counting translations through incidence graphs
-- statement:
--   Let A,B be finite structures over the same finite positive-arity relational vocabulary, all of whose arities are at most m, and let K,q>=1. Use the actual incidence construction, including every tagged tuple. Both translations hold, with the necessary positive-dimensional restriction on the second one.
--
--   $$
--   \operatorname{Inc}(A)\equiv_{C_{K+1}^{q+1}}\operatorname{Inc}(B)\Rightarrow A\equiv_{C_K^q}B,\qquad(m\ge1\ \wedge\ A\equiv_{C_{mK}^{mq}}B)\Rightarrow\operatorname{Inc}(A)\equiv_{C_K^q}\operatorname{Inc}(B).
--   $$
--
--   This result supports Theorem C.10; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
--   - correction: the second implication has no written exclusion of m=0 → m>=1 is required for the second implication only; reason: take an empty vocabulary, m=0, K=q=1, and universes of sizes 1 and 2: both structures are C_0^0-equivalent, but their incidence graphs are distinguished by the rank-one sentence counting at least two left vertices; the first implication retains m=0
--   - encoding: finite relational structures in the positive-arity vocabulary convention used by the incidence tuple range s in [m] → finite positive-arity relation-symbol types and recursively evaluated reusable-register counting formulas; reason: this implements the stated relational setting independently of homomorphism counts; empty vocabularies and empty universes are retained
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 45 (PDF p. 48), Lemma C.8; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Logic

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem lemma_C_8 (τ : Vocabulary) (m k q : ℕ)
    (hm : ∀ R, τ.arity R ≤ m) (hk : 1 ≤ k) (hq : 1 ≤ q) (A B : RelStructure τ) :
    (countingEquiv (incidence A m).structureOf (incidence B m).structureOf (k+1) (q+1) →
      countingEquiv A B k q) ∧
    (1 ≤ m → countingEquiv A B (m*k) (m*q) →
      countingEquiv (incidence A m).structureOf (incidence B m).structureOf k q) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
