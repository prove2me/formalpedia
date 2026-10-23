-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_lemma2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.lemma2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:38:44.785361+00:00
-- url     : https://prove2.me/theorems/470fb450-2058-4ce7-9da3-c1143bfbc21a
-- title:
--   Lemma 2: tripartite conditional product additivity
-- statement:
--   Let $\rho_{ABCE}$ and $\sigma_{A'B'C'E'}$ be any normalized finite-dimensional states. For their independent product and either $F=I_3$ or $F=S_3$,
--
--   $$F(AA':BB':CC'\mid EE')=F(A:B:C\mid E)_\rho+F(A':B':C'\mid E')_\sigma.$$
--
--   Corresponding honest parties and the two independent environments are paired. This is the tripartite conditional product-additivity lemma.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 6, Lemma 2: tripartite conditional product additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 2, PDF p.6,(44),(45): independent E and E', both quantities. -/
theorem lemma2 {D F : Fin 3 → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    {E Z : Type} [Fintype E] [Fintype Z] [Nonempty E] [Nonempty Z]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (sigma : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    ∀ kind : InformationKind,
      conditionalMultipartiteInformation kind (pairedProduct rho sigma) (singleParties 3) ∅ =
      conditionalMultipartiteInformation kind rho (singleParties 3) ∅ +
        conditionalMultipartiteInformation kind sigma (singleParties 3) ∅ := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
