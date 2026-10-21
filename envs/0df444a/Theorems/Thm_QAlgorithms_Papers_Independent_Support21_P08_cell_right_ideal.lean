-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_cell_right_ideal
-- name    : QAlgorithms.Papers.Independent.Support21.P08.cell_right_ideal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:25:53.422501+00:00
-- url     : https://prove2.me/theorems/81d7e942-cfd9-442d-9e0c-105e84df0719
-- title:
--   Cell modules are the seminormal right ideals
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume that the complete content sequences distinguish all tableaux, including tableaux of different shapes. Define $F_t$ by the interpolation product of Definition 3.1, $f_{st}=F_s a_{st}F_t$, and $\gamma_t$ as the coefficient of $a_{tt}$ in $f_{tt}^2$. Fix $s,t\in T(\lambda)$. There is an isomorphism of right $A$-modules, and an equality of subspaces,
--
--   $$C(\lambda)\cong f_{st}A=\operatorname{Span}_K\{f_{sv}:v\in T(\lambda)\}.$$
--
--   The isomorphism explicitly intertwines the computed right action with right multiplication; a vector-space dimension equality would be insufficient.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 12, 3.10

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

/-- Corollary 3.10, PDF p.12. Isomorphism intertwines the right action;
span equality is also retained. Uses the corrected injective separation. -/
theorem cell_right_ideal (J : JMFamily D M) (hsep : separatesAll J)
    (l : Shape) (s t : T l) :
    CellRightIso (D := D) l (rightIdealSpan (K := K) (seminormal J ⟨l, (s, t)⟩)) ∧
    rightIdealSpan (K := K) (seminormal J ⟨l, (s, t)⟩) =
      Submodule.span K (Set.range (fun v : T l => seminormal J ⟨l, (s, v)⟩)) := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
