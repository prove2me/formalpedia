-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_quasifree_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P23.quasifree_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:03:10.700625+00:00
-- url     : https://prove2.me/theorems/af5fcfe2-cff5-4ce7-aca8-13e040e311dd
-- title:
--   Proposition 6.6
-- statement:
--   Let $T\ne0$ be a positive one-particle operator on finite-dimensional $K$ with $I-T>0$, and let $\omega_T=Z_T^{-1}\Gamma(T(I-T)^{-1})$. This is a many-body state; $T$ need not have trace one. Its normal-ordered creation/annihilation moments vanish at unequal lengths and otherwise equal $\det[\langle\psi_i,T\phi_j\rangle]$, with the source’s reverse creation order. Moreover, $$\log Z_T=-\log\det(I-T)=-\operatorname{tr}\log(I-T),\quad\omega_T(\Gamma(A))=\det(I+T(A-I)),\quad\omega_T(d\Gamma(A))=\operatorname{tr}(TA).$$ Its entropy is $-\operatorname{tr}[T\log T+(I-T)\log(I-T)]$. For a second such $T_2$, $\omega_T\ll\omega_{T_2}$ exactly when $\ker T_2\subset\ker T$; then their signed relative entropy is $\operatorname{tr}[T(\log T_2-\log T)+(I-T)(\log(I-T_2)-\log(I-T))]$. The kernel direction corrects the printed typo; all six clauses remain.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 124, Proposition 6.6

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

/-- Proposition6.6, all six clauses, source PDF pp.124--125.
Corrected kernel direction in clause6: Ker T2 subset Ker T1, i.e. Supports T1 T2.
A one-mode vacuum versus faithful density disproves the printed reverse direction. -/
theorem quasifree_properties (n : ℕ) (T : Mat (Fin n))
    (hT : T.PosSemidef) (hbelow : (1-T).PosDef) (hnonzero : T ≠ 0) :
    (∀ r s : ℕ, ∀ phi : Fin r → EuclideanSpace ℂ (Fin n),
      ∀ psi : Fin s → EuclideanSpace ℂ (Fin n),
      (quasiFree T * ((List.ofFn (fun j => creation (phi j))).reverse.prod *
        (List.ofFn (fun j => annihilation (psi j))).prod)).trace =
      if h : r = s then Matrix.det (fun i j : Fin r =>
        inner ℂ (psi (Fin.cast h i)) (QAlgorithms.act T (phi j))) else 0) ∧
    Real.log (quasiFreeZ T) = -Real.log ((Matrix.det (1-T)).re) ∧
    Real.log (quasiFreeZ T) = -(logMat (1-T)).trace.re ∧
    (∀ A : Mat (Fin n), (quasiFree T * fockGamma A).trace = Matrix.det (1+T*(A-1))) ∧
    (∀ A : Mat (Fin n), (quasiFree T * dGamma A).trace = (T*A).trace) ∧
    entropy (quasiFree T) = -(T*logMat T + (1-T)*logMat (1-T)).trace.re ∧
    (∀ T2 : Mat (Fin n), T2.PosSemidef → (1-T2).PosDef → T2 ≠ 0 →
      (Supports (quasiFree T) (quasiFree T2) ↔ Supports T T2) ∧
      (Supports T T2 → signedRelativeEntropy (quasiFree T) (quasiFree T2) =
        (((T*(logMat T2-logMat T) +
          (1-T)*(logMat (1-T2)-logMat (1-T))).trace.re : ℝ) : EReal))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
