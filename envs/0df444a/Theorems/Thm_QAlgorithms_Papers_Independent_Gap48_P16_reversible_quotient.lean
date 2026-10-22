-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_reversible_quotient
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.reversible_quotient
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:00:16.251022+00:00
-- url     : https://prove2.me/theorems/0dd8893c-923e-4307-b23a-14a5d6625142
-- title:
--   Lemma 4.12
-- statement:
--   Let $R$ be a commutative noetherian unital ring. A polynomial $q\in R[x]$ is reversible if it is monic and $q(0)$ is a unit of $R$. For every such polynomial the inclusion $\iota:R[x]\to R[x,x^{-1}]$ induces a canonical $R$-algebra isomorphism
--
--   $$
--   R[x]/(q)\ \xrightarrow{\ \sim\ }\ R[x,x^{-1}]/(\iota(q)),
--   \qquad p+(q)\longmapsto\iota(p)+(\iota(q)).
--   $$
--
--   The constant polynomial $q=1$ is permitted and gives two zero quotients. This describes the precise algebra map used to compare reversible quotients.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 15, Lemma 4.12

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Laurent

variable {R : Type u} [CommRing R]

/-- Lemma 4.12, PDF pp.15-16: the quotient isomorphism induced by polynomial inclusion. -/
theorem reversible_quotient [IsNoetherianRing R] (q : Polynomial R) (hq : IsReversiblePolynomial q) :
    ∃ e : (Polynomial R ⧸ Ideal.span {q}) ≃ₐ[R]
        (LaurentPolynomial R ⧸ Ideal.span {q.toLaurent}),
      ∀ p : Polynomial R, e (Ideal.Quotient.mk (Ideal.span {q}) p) =
        Ideal.Quotient.mk (Ideal.span {q.toLaurent}) p.toLaurent := by sorry

end Laurent

end QAlgorithms.Papers.Independent.Gap48.P16

end
