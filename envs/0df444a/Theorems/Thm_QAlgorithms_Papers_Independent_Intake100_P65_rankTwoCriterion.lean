-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_rankTwoCriterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.rankTwoCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:17:45.75518+00:00
-- url     : https://prove2.me/theorems/8d0b6f6e-0042-49f1-addd-2e7f9e80500b
-- title:
--   Rank-two dimension criterion over the generic rational-function field
-- statement:
--   Let $F$ be a field with $2$ invertible and let $r\ge1$. Let $R=F(u_1,\ldots,u_r)$ be the rational-function field in algebraically independent indeterminates. Let $\Omega$ be admissible with $\omega_0\ne0$, and suppose $A=W_{r,2}(u;\Omega)$ is split semisimple. Then
--
--   $$\dim_R A=3r^2\quad\Longleftrightarrow\quad\text{$A$ has an irreducible representation of dimension $r$ on which $E$ acts nontrivially.}$$
--
--   Split semisimplicity means an isomorphism to a finite product of full matrix algebras over $R$. This is an equivalence and does not assert the existence claimed in the deferred Proposition 3.2.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 15, Theorem 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Theorem 3.4, PDF p.15, in the rational-function field on independent
indeterminates. Split semisimplicity is assumed; existence of a nontrivial-E
irreducible is the right side of the equivalence, never a premise. -/
theorem rankTwoCriterion (F : Type u) [Field F] [Invertible (2 : F)]
    (r : ℕ) (hr : 1 ≤ r)
    (omega : ℕ → FractionRing (MvPolynomial (Fin r) F))
    (ha : OmegaAdmissible omega) (hzero : omega 0 ≠ 0) :
    let R := FractionRing (MvPolynomial (Fin r) F)
    let roots : Fin r → R := fun i => algebraMap (MvPolynomial (Fin r) F) R (MvPolynomial.X i)
    let A := Cyclotomic R omega .degenerate r roots 2
    SplitMatrixAlgebra R A →
      (Module.finrank R A = 3*r^2 ↔
        ∃ rho : A →ₐ[R] Module.End R (Fin r → R),
          IrreducibleRepresentation rho ∧ rho (ce R omega .degenerate r roots 2 0) ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
