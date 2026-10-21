-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_jm_irreducible_characters
-- name    : QAlgorithms.Papers.Independent.Support21.P08.jm_irreducible_characters
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:20:31.590733+00:00
-- url     : https://prove2.me/theorems/e3a43fb3-e83e-4322-a6ad-ad51c30dd4af
-- title:
--   The irreducible representations of the JM subalgebra
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Let $\mathcal L=K[L_1,\ldots,L_M]$. This algebra is commutative. Each tableau $t$ determines a one-dimensional character $\chi_t$ and every irreducible $\mathcal L$-module is isomorphic to one of these characters:
--
--   $$\chi_t(L_i)=c_t(i).$$
--
--   Completeness is up to module isomorphism; different tableaux may give isomorphic characters. No separation is assumed. This identifies the weights used in subsequent separation arguments.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 4, 2.6

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

/-- Paragraph 2.6, PDF p.4. Every tableau gives a one-dimensional character;
all irreducible JM-algebra representations occur up to module isomorphism.
Repeated isomorphic characters are allowed, and separation is NOT assumed. -/
theorem jm_irreducible_characters (J : JMFamily D M) :
    (∀ a b : jmAlgebra J, a * b = b * a) ∧
    ∃ chi : CellTableau Shape T → (jmAlgebra J →ₐ[K] K),
      (∀ t i, chi t (jmGenerator J i) = J.content t i) ∧
      (∀ (V : Type*) [AddCommGroup V] [Module K V]
        (rho : jmAlgebra J →ₐ[K] Module.End K V),
        IrreducibleRepresentation rho →
        ∃ t : CellTableau Shape T, ∃ e : V ≃ₗ[K] K,
          ∀ a v, e (rho a v) = chi t a * e v) := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
