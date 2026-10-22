-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_split_family_markov
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.split_family_markov
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:43:20.971925+00:00
-- url     : https://prove2.me/theorems/8b316d96-0c65-40dc-a6ed-ef323ee93fe5
-- title:
--   Split-middle Markov covariances with nonproduct examples
-- statement:
--   Let $H_2=K_a\oplus K_b$. Let $L\ge0$ act on $H_1\oplus K_a$, and let $R\ge0$ act on $K_b\oplus H_3$, all spaces being finite-dimensional complex Hilbert spaces. Reindex $A=L\oplus R$ into the time order $H_1,(K_a\oplus K_b),H_3$. Then
--
--   $$A\ge0,\qquad S(\omega_A)-S(\omega_{A_{23,23}})=S(\omega_{A_{12,12}})-S(\omega_{A_{22}}).$$
--
--   If both $L$ and $R$ are positive definite, $A$ also satisfies the exact ordered identity (40) for every real parameter. Taking $H_1=K_a=K_b=H_3=\mathbb C$ and
--
--   $$L=R=\begin{pmatrix}2&1/2\\1/2&2\end{pmatrix}$$
--
--   gives a positive-definite Markov covariance with both neighbouring blocks $A_{12}$ and $A_{23}$ nonzero. Thus the state is not a product in the original time localization. This realizes the introduction's nontrivial existence claim; the Markov entropy is evaluated by $\operatorname{Tr}g$ as in Theorem 1.3.
--
--   Write $B=\operatorname{diag}(A_{12,12},I_3)$, $C=\operatorname{diag}(I_1,A_{22},I_3)$ and $D=\operatorname{diag}(I_1,A_{23,23})$ on the same time space. The ordered identity (40) means
--
--   $$A^{it}(I+A)^{-it}D^{-it}(I+D)^{it}=B^{it}(I+B)^{-it}C^{-it}(I+C)^{it}\quad(t\in\mathbb R).$$
--
--   All these powers in the stated uses have strictly positive spectra.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 14, Example 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

/-- Example 2.1, PDF pp.14–15, and the existence claim on p.3: the whole positive
split family is Markov, including zero modes. The concrete member has both
neighbouring covariance blocks nonzero, hence is not a product in time localization. -/
theorem split_family_markov {Ja Jb : Type*} [Fintype Ja] [Fintype Jb]
    [DecidableEq Ja] [DecidableEq Jb] (L : Mat (I ⊕ Ja)) (R : Mat (Jb ⊕ K))
    (hL : L.PosSemidef) (hR : R.PosSemidef) :
    (splitCovariance L R).PosSemidef ∧ IsMarkov (splitCovariance L R) ∧
    (L.PosDef → R.PosDef → PowerCondition (splitCovariance L R)) ∧
    (let A := splitCovariance correlatedPair correlatedPair
     A.PosDef ∧ IsMarkov A ∧ a12 A ≠ 0 ∧ a23 A ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
