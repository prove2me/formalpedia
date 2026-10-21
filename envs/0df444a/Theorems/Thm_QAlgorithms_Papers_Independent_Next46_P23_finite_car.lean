-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_finite_car
-- name    : QAlgorithms.Papers.Independent.Next46.P23.finite_car
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:01:42.461871+00:00
-- url     : https://prove2.me/theorems/dc9fe6a0-eeba-478a-a653-80fcbcffefca
-- title:
--   Proposition 6.2
-- statement:
--   On fermionic Fock space over finite-dimensional $K$, creation $a^*(\psi)$ wedges on the left and annihilation is its adjoint. Creation is linear and annihilation anti-linear, and $$\{a(\psi),a(\phi)\}=\{a^*(\psi),a^*(\phi)\}=0,\qquad\{a(\psi),a^*(\phi)\}=\langle\psi,\phi\rangle I.$$ The representation is irreducible and both operator norms equal $\|\psi\|$. For every $A$, $\Gamma(A)a^*(\psi)=a^*(A\psi)\Gamma(A)$ and $\Gamma(A^*)a(A\psi)=a(\psi)\Gamma(A^*)$, yielding unitary covariance. The commutators with $d\Gamma(A)$ are $a^*(A\psi)$ and $-a(A^*\psi)$; for self-adjoint $A$, multiplication of either commutator by $i$ gives $a^\#(iA\psi)$. Also $a^*(\phi)a(\psi)=d\Gamma(|\phi\rangle\langle\psi|)$ and, in any orthonormal basis, $d\Gamma(A)=\sum_{j,k}\langle\psi_j,A\psi_k\rangle a^*(\psi_j)a(\psi_k)$. All nine clauses are stated.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 119, Proposition 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Proposition6.2, all nine clauses, source PDF pp.119--120.
Creation is linear, annihilation anti-linear, and clause9 sums both basis indices. -/
theorem finite_car (n : ℕ) :
    (∀ psi phi : EuclideanSpace ℂ (Fin n), ∀ c : ℂ,
      creation (psi+phi) = creation psi + creation phi ∧
      creation (c • psi) = c • creation psi ∧
      annihilation (psi+phi) = annihilation psi + annihilation phi ∧
      annihilation (c • psi) = conj c • annihilation psi) ∧
    (∀ psi : EuclideanSpace ℂ (Fin n), (annihilation psi)ᴴ = creation psi) ∧
    (∀ psi phi : EuclideanSpace ℂ (Fin n),
      annihilation psi * annihilation phi + annihilation phi * annihilation psi = 0 ∧
      creation psi * creation phi + creation phi * creation psi = 0 ∧
      annihilation psi * creation phi + creation phi * annihilation psi = (inner ℂ psi phi) • 1) ∧
    (∀ B : Mat (FermionOccupation n),
      (∀ psi : EuclideanSpace ℂ (Fin n), B * creation psi = creation psi * B ∧
        B * annihilation psi = annihilation psi * B) → ∃ c : ℂ, B = c • 1) ∧
    (∀ psi : EuclideanSpace ℂ (Fin n),
      QAlgorithms.specNorm (creation psi) = ‖psi‖ ∧ QAlgorithms.specNorm (annihilation psi) = ‖psi‖) ∧
    ((∀ A : Mat (Fin n), ∀ psi : EuclideanSpace ℂ (Fin n),
      fockGamma A * creation psi = creation (QAlgorithms.act A psi) * fockGamma A ∧
      fockGamma (Aᴴ) * annihilation (QAlgorithms.act A psi) = annihilation psi * fockGamma (Aᴴ)) ∧
      (∀ U : Matrix.unitaryGroup (Fin n) ℂ, ∀ psi : EuclideanSpace ℂ (Fin n),
        fockGamma (U : Mat (Fin n)) * creation psi * fockGamma (U : Mat (Fin n))ᴴ =
          creation (QAlgorithms.act (U : Mat (Fin n)) psi) ∧
        fockGamma (U : Mat (Fin n)) * annihilation psi * fockGamma (U : Mat (Fin n))ᴴ =
          annihilation (QAlgorithms.act (U : Mat (Fin n)) psi))) ∧
    ((∀ A : Mat (Fin n), ∀ psi : EuclideanSpace ℂ (Fin n),
      dGamma A * creation psi - creation psi * dGamma A = creation (QAlgorithms.act A psi) ∧
      dGamma A * annihilation psi - annihilation psi * dGamma A = -annihilation (QAlgorithms.act (Aᴴ) psi)) ∧
      (∀ A : Mat (Fin n), A.IsHermitian → ∀ psi : EuclideanSpace ℂ (Fin n),
        Complex.I • (dGamma A * creation psi - creation psi * dGamma A) =
          creation (Complex.I • QAlgorithms.act A psi) ∧
        Complex.I • (dGamma A * annihilation psi - annihilation psi * dGamma A) =
          annihilation (Complex.I • QAlgorithms.act A psi))) ∧
    (∀ phi psi : EuclideanSpace ℂ (Fin n),
      creation phi * annihilation psi = dGamma (fun i j => phi i * conj (psi j))) ∧
    (∀ A : Mat (Fin n), ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      dGamma A = ∑ j, ∑ k, (inner ℂ (b j) (QAlgorithms.act A (b k))) •
        (creation (b j) * annihilation (b k))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
