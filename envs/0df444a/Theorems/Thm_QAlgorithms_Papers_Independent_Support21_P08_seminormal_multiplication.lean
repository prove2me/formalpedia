-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_seminormal_multiplication
-- name    : QAlgorithms.Papers.Independent.Support21.P08.seminormal_multiplication
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:24:50.140536+00:00
-- url     : https://prove2.me/theorems/2357b1ed-769c-40d7-95ea-1e85f2e55c7e
-- title:
--   The seminormal multiplication law and cellular basis
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume that the complete content sequences distinguish all tableaux, including tableaux of different shapes. Define $F_t$ by the interpolation product of Definition 3.1, $f_{st}=F_s a_{st}F_t$, and $\gamma_t$ as the coefficient of $a_{tt}$ in $f_{tt}^2$. The computed structure coefficient depends only on $t$. For $s,t\in T(\lambda)$ and $u,v\in T(\mu)$,
--
--   $$f_{st}^{\lambda}f_{uv}^{\mu}=\begin{cases}\gamma_t f_{sv}^{\lambda},&\lambda=\mu\text{ and }t=u,\\0,&\text{otherwise}.\end{cases}$$
--
--   Moreover the seminormal vectors form a cellular basis for the same involution and cell order. Neither the scalars nor their multiplication law are postulated as hypotheses.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 11, 3.7

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

/-- Theorem 3.7, PDF p.11. Gamma is defined by coordinates, not assumed.
Same-shape and cross-shape products together give the entire displayed law.
Separation is the stronger injective reading used on p.10. -/
theorem seminormal_multiplication (J : JMFamily D M) (hsep : separatesAll J) :
    (∀ l (s t u v : T l),
      seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨l, (u, v)⟩ =
        if t = u then seminormalGamma J ⟨l, t⟩ • seminormal J ⟨l, (s, v)⟩ else 0) ∧
    (∀ l m, l ≠ m → ∀ (s t : T l) (u v : T m),
      seminormal J ⟨l, (s, t)⟩ * seminormal J ⟨m, (u, v)⟩ = 0) ∧
    IsCellularFamily D (seminormal J) := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
