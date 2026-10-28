-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_rankOne_kraus_orthogonal_rows_series
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.rankOne_kraus_orthogonal_rows_series
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:06:51.670258+00:00
-- url     : https://prove2.me/theorems/10ac2ba4-53e9-423c-ac75-bf10384a7dc9
-- title:
--   Rank-one Kraus representation regroups into orthogonal spectral rows
-- statement:
--   Let $\Psi$ have a Kraus representation by rank-one operators $|\varphi_{ij}\rangle\langle w_i|$, $j$ ranging over an index set of size $m$, with $\sum_j\|\varphi_{ij}\|^2=1$ for every $i$. Then there are rows $\psi_{ik}$ that are mutually orthogonal within each row with $\sum_k\|\psi_{ik}\|^2=1$ (eigenvectors of $\sigma_i=\sum_j|\varphi_{ij}\rangle\langle\varphi_{ij}|$), such that $\sigma_i=\sum_k|\psi_{ik}\rangle\langle\psi_{ik}|$ in trace norm and
--   $$\Psi(X)=\sum_i\langle w_i|X|w_i\rangle\,\sigma_i$$
--   in trace norm for every trace-class $X$.
--
--   Role: the spectral regrouping that gives the whitened normal form (clauses 3-4 of HasWhitenedForm) in the parent's r = 1 clause.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, proof of Theorem 3, case r = 1 (PDF pp. 8-9, the representation Psi(rho) = sum_i <w_i|rho|w_i> sigma_i, equation (8)); spectral theorem for positive compact (trace-class) operators (standard, e.g. Reed-Simon I, Theorem VI.17)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

theorem rankOne_kraus_orthogonal_rows_series
    {I E L : Type} [Countable L] (m : ℕ∞) (Psi : Channel I E) (w : L → Hilbert I)
    (phi : L → BoundIndex m → Hilbert E) (hphi : ∀ i, HasSum (fun j => ‖phi i j‖ ^ 2) 1)
    (hK : IsKrausRepresentation Psi.val (fun p : L × BoundIndex m =>
      ((innerSL ℂ (w p.1)).smulRight (phi p.1 p.2) : Hilbert I →L[ℂ] Hilbert E))) :
    ∃ psi : L → BoundIndex m → Hilbert E, NormalizedOrthogonalRows psi ∧
      ∃ sigma : L → Matrix E E ℂ,
        (∀ i, coefficientTraceHasSum (fun k => rankOne (psi i k)) (sigma i)) ∧
        ∀ X, IsTraceClass X → coefficientTraceHasSum (fun i => boundedTracePair X
          (boundedOperator (rankOne (w i))) • sigma i) (Psi.val X) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
