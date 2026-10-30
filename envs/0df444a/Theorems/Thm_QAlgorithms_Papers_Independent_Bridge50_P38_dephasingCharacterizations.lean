-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P38_dephasingCharacterizations
-- name    : QAlgorithms.Papers.Independent.Bridge50.P38.dephasingCharacterizations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:38:21.065991+00:00
-- url     : https://prove2.me/theorems/24e08cde-a223-4190-a878-821855dc7f0d
-- title:
--   Dephasing a maximally entangled state and averaging clock powers
-- statement:
--   Let $d\ge1$, let $U$ be unitary, let $u_i=U|i\rangle\langle i|U^\dagger$, and set $T_U(X)=\sum_i u_iXu_i$. Conjugation of vectors and matrices is in the fixed computational basis. Define the normalized maximally entangled state $|\Phi_d\rangle=d^{-1/2}\sum_{i=1}^d|i\rangle|i\rangle$ and the clock by $Z_U U|i\rangle=e^{2\pi\mathrm i i/d}U|i\rangle$. Then
--
--   $$(T_U\otimes\operatorname{id})(\Phi_d)=\frac1d\sum_{i=1}^d u_i\otimes\overline{u_i},\qquad T_U(\rho)=\frac1d\sum_{j=0}^{d-1}Z_U^j\rho Z_U^{-j}$$
--
--   for every density matrix $\rho$. Here $\Phi_d$ in the formula denotes its rank-one density matrix, and $\overline{u_i}$ is the projector onto the conjugate vector. These are the two source characterizations of the same dephasing map.
-- source:
--   Decoding quantum information via the Petz recovery map, arXiv:1504.04449v4, PDF p. 10, lemma-3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Bridge50.P38

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P63 (normalQuantile)

open QAlgorithms.Papers.Independent.Dependency50.P36
  (relativeEntropyFinite pairInformationVariance)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (columnProjector pinch marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification singleUseInformation coherentInformation)

open QAlgorithms.Papers.Independent.Gap48.P23 (CompletelyPositive)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- PDF p.10, Lemma 3.3, BOTH clauses: conjugated second factor of the
maximally entangled dephasing, and the finite clock-conjugation average. -/
theorem dephasingCharacterizations (d : ℕ) [NeZero d]
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    firstAction (T := Fin d) (pinch (U : Matrix (Fin d) (Fin d) ℂ)) (pureDensity (finiteMaxEntangled (Fin d))) =
      ((d : ℂ)⁻¹) • ∑ i, Matrix.kronecker (columnProjector (U : Matrix (Fin d) (Fin d) ℂ) i)
        (fun a b => conj (columnProjector (U : Matrix (Fin d) (Fin d) ℂ) i a b)) ∧
    ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
      pinch (U : Matrix (Fin d) (Fin d) ℂ) rho = ((d : ℂ)⁻¹) •
        ∑ j : Fin d, conjSuperop (basisClock U ^ j.val) rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P38

end
