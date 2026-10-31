-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_classical_test_bounds
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.classical_test_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:34:41.073955+00:00
-- url     : https://prove2.me/theorems/ca2756b1-fdc9-4476-a710-5241d3faed8d
-- title:
--   Lemma 16: Classical Neyman–Pearson test bounds
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. Let $\rho_{AB},\tau_A$ be states with $\rho_A\ll\tau_A$, $d=|B|\ge1$, $n\ge0$ and $\mu\in\mathbb R$. Put $K=\tau_A^{\otimes n}\otimes\omega_n$, $L=\mathcal P_K(\rho_{AB}^{\otimes n})$, and $T=\{L\ge e^\mu K\}$. Choose any common orthonormal eigenbasis $(\phi_x)$ of $L,K$ and define the probability laws $P(x)=\langle\phi_x,L\phi_x\rangle$ and $Q(x)=\langle\phi_x,K\phi_x\rangle$. Then
--   $$\alpha(T;\rho_{AB}^{\otimes n})=\sum_{P(x)<e^\mu Q(x)}P(x),\qquad \beta(T;\tau_A^{\otimes n})\le g_{n,d}\sum_{P(x)\ge e^\mu Q(x)}Q(x).$$
--   Here $\beta$ maximizes acceptance over all normalized $B^n$ alternatives, and $g_{n,d}=\binom{n+d^2-1}{n}$. Zero threshold eigenvalues are accepted. These bounds reduce the constructed joint test to classical tail events.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 16, Lemma 16: Classical Neyman–Pearson test bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF p.16, Lemma 16, (6.4)--(6.7).
The law Q is distinct from the test. Rejection is strict and acceptance non-strict,
so zero-eigenvalue outcomes are accepted. n=0 is allowed here. -/
theorem classical_test_bounds [Nonempty A] (d : ℕ) (hd : 0 < d)
    (rho : Op (A × Fin d)) (tau : Op A) (hr : IsDensityMatrix rho)
    (ht : IsDensityMatrix tau) (hS : SupportLE (traceRight rho) tau) (n : ℕ) (mu : ℝ)
    (U : Matrix.unitaryGroup ((Fin n → A) × (Fin n → Fin d)) ℂ)
    (hL : DiagonalIn (U : Op _) (classicalNull n rho tau))
    (hK : DiagonalIn (U : Op ((Fin n → A) × (Fin n → Fin d)))
      (universalReference (d := d) n tau)) :
    let L := classicalNull n rho tau
    let K := universalReference (d := d) n tau
    let P := basisLaw L U
    let Q := basisLaw K U
    let T := thresholdTest L K mu
    rejectionError (groupedCopies n rho) T =
      (∑ x, if P x < Real.exp mu * Q x then P x else 0) ∧
    compositeAcceptanceError (copies n tau) T ≤ (universalFactor n d : ℝ) *
      ∑ x, if Real.exp mu * Q x ≤ P x then Q x else 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
