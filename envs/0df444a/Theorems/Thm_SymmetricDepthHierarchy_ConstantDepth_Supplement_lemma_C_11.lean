-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_C_11
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_C_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:05:29.94243+00:00
-- url     : https://prove2.me/theorems/e0a6cab6-d7ee-45ca-9f22-d00ad265a0b0
-- title:
--   Lemma C.11 — Tunable counting-logic round bounds
-- statement:
--   There are integers ell_0>=3 and xi>=1 such that for every h>=ell_0 and r>=1, two equal-size finite structures over one finite vocabulary of arity at most ell_0 satisfy the following three conditions. The size bound is a product, not an exponential.
--
--   $$
--   |A|=|B|\le2\xi h^2r,\qquad A\equiv_{C_h^r}B,\qquad A\not\equiv_{C_{\ell_0}^{\xi hr}}B.
--   $$
--
--   This result supports Theorem 5.7; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
--   - encoding: constants l_0>=3 and xi>=1 → natural-number constants l_0>=3 and xi>=1; reason: the proof permits enlarging xi to an integer; the size bound increases and non-equivalence remains true at the larger rank
--   - encoding: finite relational structures in the positive-arity vocabulary convention used by the incidence tuple range s in [m] → finite positive-arity relation-symbol types and recursively evaluated reusable-register counting formulas; reason: this implements the stated relational setting independently of homomorphism counts; empty vocabularies and empty universes are retained
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 47 (PDF p. 50), Lemma C.11; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Logic

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem lemma_C_11 : ∃ l₀ ξ : ℕ, 3 ≤ l₀ ∧ 1 ≤ ξ ∧
    ∀ h r : ℕ, l₀ ≤ h → 1 ≤ r →
      ∃ τ : Vocabulary, (∀ R, τ.arity R ≤ l₀) ∧
      ∃ A B : RelStructure τ,
        Fintype.card A.U = Fintype.card B.U ∧ Fintype.card A.U ≤ 2*ξ*h^2*r ∧
        countingEquiv A B h r ∧ ¬ countingEquiv A B l₀ (ξ*h*r) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
