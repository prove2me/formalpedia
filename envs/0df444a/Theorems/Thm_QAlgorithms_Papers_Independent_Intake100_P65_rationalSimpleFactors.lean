-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_rationalSimpleFactors
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.rationalSimpleFactors
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:20:25.239091+00:00
-- url     : https://prove2.me/theorems/37e855b2-70e4-4b50-a8cc-608dc0bbdc09
-- title:
--   Finite simple affine actions factor through admissible cyclotomic quotients
-- statement:
--   Let $R$ be an algebraically closed field with $2$ invertible, $n\ge1$, and let $\Omega$ be admissible and rational. Rationality means that $\sum_a\omega_a z^a$ is the expansion of a rational function at $z=0$, with nonzero denominator constant coefficient, equivalently an eventual linear recurrence. For every specified finite-dimensional irreducible $W_n^{\mathrm{aff}}(\Omega)$-action $\rho$ on $V$, there exist $r\ge1$, $u\in R^r$ with $\Omega$ $u$-admissible, and an irreducible action $\sigma$ of $W_{r,n}(u;\Omega)$ on the same $V$ such that
--
--   $$\sigma(\pi_{r,n}(a))=\rho(a)\quad\text{for every }a\in W_n^{\mathrm{aff}}(\Omega).$$
--
--   Furthermore, there exist some $r\ge1$ and $u\in R^r$ for which $\Omega$ is $u$-admissible. The parameters in the factorization may depend on the original action.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 16, Proposition 3.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Proposition 3.11, PDF pp.16--17. The existing finite-dimensional simple
action factors through a u-admissible quotient; parameters may depend on it.
The final existence assertion for Omega is retained separately. -/
theorem rationalSimpleFactors (R : Type u) [Field R] [IsAlgClosed R]
    [Invertible (2 : R)] (omega : ℕ → R) (n : ℕ) (hn : 1 ≤ n)
    (ha : OmegaAdmissible omega) (hrat : RationalSequence omega) :
    (∀ (V : Type u) [AddCommGroup V] [Module R V] [FiniteDimensional R V]
      (rho : AffineBMW R omega n →ₐ[R] Module.End R V),
      IrreducibleRepresentation rho →
        ∃ (r : ℕ) (roots : Fin r → R), 1 ≤ r ∧ RootAdmissible omega roots ∧
          ∃ sigma : Cyclotomic R omega .degenerate r roots n →ₐ[R] Module.End R V,
            (∀ a : AffineBMW R omega n,
              sigma (affineCyclotomicProjection R omega n r roots hn a) = rho a) ∧
            IrreducibleRepresentation sigma) ∧
    (∃ (r : ℕ) (roots : Fin r → R), 1 ≤ r ∧ RootAdmissible omega roots) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
