-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_comparable_separation_split
-- name    : QAlgorithms.Papers.Independent.Support21.P08.comparable_separation_split
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:21:51.898821+00:00
-- url     : https://prove2.me/theorems/369e1d4b-c4cb-437c-89f6-2f2fa9bcf0c4
-- title:
--   Comparable separation implies split semisimplicity
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Suppose distinct comparable tableaux have different content sequences, exactly as in printed Definition 2.8. Then $A$ is split semisimple: there are finitely many positive integers $d_1,\ldots,d_r$ with
--
--   $$A\cong_K\prod_{j=1}^r\operatorname{Mat}_{d_j}(K).$$
--
--   The conclusion includes splitting over $K$, rather than only semisimplicity as a ring.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 4, 2.9

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section SeparatedDefinitions

variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]

variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}

variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

/-- Corollary 2.9, PDF p.4. This keeps the printed comparable-pair separation;
it does not replace it by complete-sequence injectivity. -/
theorem comparable_separation_split (J : JMFamily D M)
    (hsep : separatesComparable J) : SplitSemisimple (K := K) (A := A) := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
