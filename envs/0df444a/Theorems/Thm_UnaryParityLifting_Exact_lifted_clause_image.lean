-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_lifted_clause_image
-- name    : UnaryParityLifting.Exact.lifted_clause_image
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:30.984114+00:00
-- url     : https://prove2.me/theorems/5797ac2c-4f5c-488a-bec2-c1865e61c56c
-- title:
--   Lemma 3.7 — Image of a lifted clause
-- statement:
--   Let $g$ be a surjective 1-stifling gadget as in the standing setting of Section 3.2. Let $C$ be any non-tautological ordinary clause, including the empty clause. Let $\xi$ be a block assignment whose gadget outputs falsify $C$, and let $D_{C,\xi}$ be the lifted clause excluding $\xi$ on those blocks. With $\zeta_C$ the falsifying assignment of $C$,
--   $$A_g\overline{D_{C,\xi}}=\theta_C\overline C,\qquad \theta_C=\prod_{i\in\mathrm{vars}(C)}|g^{-1}(\zeta_C(i))|^{-1},\qquad 0<\theta_C\le1.$$
--
--   This preserves the actual fiber sizes for biased gadgets. Assignments outside the supported blocks do not affect the lifted clause. For an empty clause the product is one. The result identifies the exact coefficients on the axiom side after averaging.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [N] and [m], bits in {0,1} → Fin N and Fin m, Bool bits with false = 0 and true = 1; reason: zero-based labels and the explicit bit maps preserve every assignment
--   - encoding: surjective gadget convention of Definition 2.5, retained throughout Sections 3–4 → an explicit Function.Surjective g hypothesis; reason: excludes empty gadget fibers and the zero-bit vacuity of the reused stifling predicate without excluding any source gadget
--   - encoding: xi defined only on blocks of vars(C) → a full block assignment whose outputs falsify C; reason: its coordinates outside those blocks are ignored by liftClause, and every partial xi extends to such a full assignment
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; p.10, Lemma 3.7, equation (3.6); p.8, Definition 2.5

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_averaging

namespace UnaryParityLifting.Exact

/-- Alekseev, STOC 2027 submission #567 (October 2026), p.10, Lemma 3.7.
The 1-stifling context is the preamble of §3.2. -/
theorem lifted_clause_image (m N : ℕ) (g : (Fin m → Bool) → Bool)
    (hg : Function.Surjective g) (hstifling : LiftSAParity.IsOneStifling g)
    (C : LiftSAParity.Clause (Fin N)) (hC : NoTautology C)
    (ξ : Fin N × Fin m → Bool) (hξ : LiftSAParity.Falsifies (blockMap g ξ) C) :
    0 < clauseTheta g C ∧ clauseTheta g C ≤ 1 ∧
      average g (clauseIndicator (LiftSAParity.liftClause C ξ)) =
        fun z => clauseTheta g C * clauseIndicator C z := by sorry

end UnaryParityLifting.Exact
