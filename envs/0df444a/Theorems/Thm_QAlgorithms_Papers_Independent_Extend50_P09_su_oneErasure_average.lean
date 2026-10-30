-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_su_oneErasure_average
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.su_oneErasure_average
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:46:05.566968+00:00
-- url     : https://prove2.me/theorems/77782e40-85ee-48c7-a3d0-8e1efdf6be30
-- title:
--   Appendix D: exact one-erasure averaged channel
-- statement:
--   Fix an integer $d\ge2$. For $n\ge2$ let $\lambda$ partition $n-1$ with at most $d$ rows, and let $l_\lambda,r_\lambda$ be the actual Schur and Specht module dimensions. Append the physical isotypic embedding of $I_{L_\lambda}/l_\lambda\otimes|\psi_\lambda\rangle\langle\psi_\lambda|$, where $\psi_\lambda$ is a fixed unit Specht vector, to one logical $d$-level system. Conjugate by Haar measure on the determinant-one commutant of the collective $SU(d)$ action and erase one fixed known site. Errors mean optimal CPTP recovery measured in root-fidelity purified distance, with normalized Choi input and a decoder chosen before the worst reference-entangled input.
--
--   For every logical operator $X$, the ensemble-averaged single erased-qudit output channel is exactly
--   $$\mathcal C_n(X)=\frac Xn+\frac{n-1}{n}\operatorname{Tr}(X)\frac{I_d}{d}.$$
--   For every reference-logical operator $Y^{RL}$ its reference extension is
--   $$(\mathrm{id}_R\otimes\mathcal C_n)(Y)=\frac Yn+\frac{n-1}{n}\operatorname{Tr}_L(Y)\otimes\frac{I_d}{d}.$$
--
--   This is an equality of the averaged physical channel, independent of $\lambda$ after constructing its allowed ancilla, and is not an equality for each individual encoding unitary.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 12, Appendix D: exact one-erasure averaged channel

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Appendix D, PDF p.22, (D12)–(D14): equality of the averaged
one-erasure CHANNEL, for every operator, with its full reference extension.
The reference factor is its actual marginal, not always I/d. -/
theorem su_oneErasure_average (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (lam : Schur.Partition d (n-1))
    (psi : EuclideanSpace ℂ (Fin (rdim lam))) (hpsi : IsState psi)
    (mu : Measure (Op (CovariantWord d n))) (hmu : IsCommutantHaarLaw (SUGroup d n) mu) :
    (∀ X : Op (Fin d), ∀ a b : Fin d,
      firstTrace (show 1 ≤ n by omega)
        (∫ V, appendUnitaryEncoder (show 1 ≤ n by omega) (suAncilla lam psi) V (logicalMatrix X) ∂mu)
        (fun _ => a) (fun _ => b) = oneErasureMeanChannel d n X a b) ∧
    (∀ X : Op (Fin d × Fin d),
      idTensorSuperop (R := Fin d) (oneErasureMeanChannel d n) X =
        (n : ℂ)⁻¹ • X + (((n : ℂ)-1)/(n : ℂ)) •
          Matrix.kronecker (traceRight X) (mixed (Fin d))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
