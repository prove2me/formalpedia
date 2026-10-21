-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_symmetric_jm_central
-- name    : QAlgorithms.Papers.Independent.Support21.P08.symmetric_jm_central
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:30:36.616049+00:00
-- url     : https://prove2.me/theorems/0ee384eb-6f4d-4145-83c1-6e9787c29093
-- title:
--   Symmetric JM polynomials are central after reduction
-- statement:
--   Let $R$ be a discrete valuation domain, $K$ its fraction field, and $k=R/\mathfrak m$ its canonical residue field. Let $A_R,A_K,A_k$ be the same cellular algebra under the basis-compatible scalar extensions, with JM elements whose complete generic content sequences are injective. Write $s\approx t$ for equality of all reduced contents. Put $F_{[t]}=\sum_{u\approx t}F_u$ and let $G_{[t]}$ be its reduction after integrality. Suppose that within each cell shape the MULTISET of contents $\{c_t(1),\ldots,c_t(M)\}$ is independent of $t$. For every polynomial $p\in k[X_1,\ldots,X_M]$ invariant under every permutation of the variables,
--
--   $$p(\overline L_1,\ldots,\overline L_M)\in Z(A_k).$$
--
--   Multiplicities are essential: equality of underlying supports would not suffice. Centrality is concluded for every symmetric polynomial over $k$, rather than assumed.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 20, 4.13

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section ResidueIntegrality

variable {R K AR AK Shape : Type*} [CommRing R] [modularDomain : IsDomain R]

variable [modularDVR : IsDiscreteValuationRing R] [Field K] [Algebra R K] [modularFraction : IsFractionRing R K]

variable [Ring AR] [Algebra R AR] [Ring AK] [Algebra K AK] [Algebra R AK]

variable [modularTower : IsScalarTower R K AK] [Fintype Shape] [PartialOrder Shape]

variable {T : Shape → Type*} [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable {B : Type*} [Ring B] [Algebra (IsLocalRing.ResidueField R) B] {M : ℕ}

section ModularStatements

include modularDomain modularDVR modularFraction modularTower

/-- Proposition 4.13, PDF pp.20–21. Braces mean MULTISETS: the proof
requires equality under every symmetric polynomial, and equality of supports
would be false. Constancy of the multiset within each shape is equivalent to
the source's existential c_lambda list, including empty cells. Centrality is
a conclusion for EVERY symmetric polynomial over the residue field.
Uses corrected complete content-sequence separation. -/
theorem symmetric_jm_central
    (S : ModularSystem (R := R) (K := K) (AR := AR) (AK := AK) (T := T) B M)
    (hsep : separatesAll S.integralJM)
    (hcontent : ∀ l (s t : T l),
      (List.ofFn (S.integralJM.content ⟨l, s⟩) : Multiset R) =
      (List.ofFn (S.integralJM.content ⟨l, t⟩) : Multiset R))
    (p : MvPolynomial (Fin M) (IsLocalRing.ResidueField R))
    (hsym : SymmetricPolynomial p) :
    Central (orderedPolynomialEval p (fun i => S.reduction (S.integralJM.L i))) := by sorry

end ModularStatements

end ResidueIntegrality

end QAlgorithms.Papers.Independent.Support21.P08

end
