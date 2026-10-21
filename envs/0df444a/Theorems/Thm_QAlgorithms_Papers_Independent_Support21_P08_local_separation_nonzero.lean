-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_local_separation_nonzero
-- name    : QAlgorithms.Papers.Independent.Support21.P08.local_separation_nonzero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:21:11.643994+00:00
-- url     : https://prove2.me/theorems/6dd81b65-3e75-4d21-bc62-b701d34d3f3c
-- title:
--   Local comparable separation detects a nonzero cell quotient
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Fix $\lambda\in\Lambda$ and $s\in T(\lambda)$. Suppose that for every tableau $t$ strictly dominated by $s$, some $i$ satisfies $c_t(i)\ne c_s(i)$. Then the cell form is nonzero, equivalently
--
--   $$D(\lambda)=C(\lambda)/\operatorname{rad}C(\lambda)\ne0.$$
--
--   The Lean conclusion gives vectors with nonzero pairing, exactly the nonzero-radical-quotient assertion. This keeps the source's local hypothesis.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 4, 2.7

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

/-- Proposition 2.7, PDF p.4. Keep the LOCAL comparable-pair hypothesis at s.
Nonzero form is equivalent to the radical quotient D(lambda) being nonzero. -/
theorem local_separation_nonzero (J : JMFamily D M) (l : Shape) (s : T l)
    (hsep : ∀ t : CellTableau Shape T, tabDominates ⟨l, s⟩ t → ⟨l, s⟩ ≠ t →
      ∃ i, J.content t i ≠ J.content ⟨l, s⟩ i) :
    ∃ v w : T l → K, cellForm D l v w ≠ 0 := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
