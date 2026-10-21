-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_seminormal_eigen_projection
-- name    : QAlgorithms.Papers.Independent.Support21.P08.seminormal_eigen_projection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:24:09.310729+00:00
-- url     : https://prove2.me/theorems/2401fea2-b084-452d-bb59-8e465e0f5989
-- title:
--   JM eigenvalues and spectral projection on seminormal vectors
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume that the complete content sequences distinguish all tableaux, including tableaux of different shapes. Define $F_t$ by the interpolation product of Definition 3.1, $f_{st}=F_s a_{st}F_t$, and $\gamma_t$ as the coefficient of $a_{tt}$ in $f_{tt}^2$. For $s,t\in T(\lambda)$, every tableau $u$, and every $i$,
--
--   $$f_{st}L_i=c_t(i)f_{st},\quad L_if_{st}=c_s(i)f_{st},\quad f_{st}F_u=\delta_{tu}f_{st},\quad F_uf_{st}=\delta_{us}f_{st}.$$
--
--   The delta formulation is the equivalent well-typed version at the end of the source proof.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 9, 3.4

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

/-- Proposition 3.4(a–d), PDF pp.9–10. The proof uses injective complete
sequences, stronger than printed Definition 2.8. Delta is expressed without
ill-typed cross-shape subscripts, as at the end of the source's proof. -/
theorem seminormal_eigen_projection (J : JMFamily D M) (hsep : separatesAll J) :
    (∀ l (s t : T l) i,
      seminormal J ⟨l, (s, t)⟩ * J.L i = J.content ⟨l, t⟩ i • seminormal J ⟨l, (s, t)⟩) ∧
    (∀ l (s t : T l) i,
      J.L i * seminormal J ⟨l, (s, t)⟩ = J.content ⟨l, s⟩ i • seminormal J ⟨l, (s, t)⟩) ∧
    (∀ l (s t : T l) u,
      seminormal J ⟨l, (s, t)⟩ * jmSpectralProjector J u =
        if u = ⟨l, t⟩ then seminormal J ⟨l, (s, t)⟩ else 0) ∧
    (∀ l (s t : T l) u,
      jmSpectralProjector J u * seminormal J ⟨l, (s, t)⟩ =
        if u = ⟨l, s⟩ then seminormal J ⟨l, (s, t)⟩ else 0) := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
