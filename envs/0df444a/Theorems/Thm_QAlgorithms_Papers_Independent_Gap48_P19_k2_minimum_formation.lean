-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P19_k2_minimum_formation
-- name    : QAlgorithms.Papers.Independent.Gap48.P19.k2_minimum_formation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:10:54.193539+00:00
-- url     : https://prove2.me/theorems/1c5e11fb-eca3-4640-8a68-ac0c43c095dc
-- title:
--   The K2 minimum equals twice Bennett formation
-- statement:
--   Let $\rho_{AB}$ be a density matrix on two nonzero finite complex Hilbert spaces. Let $K_2(\rho)$ contain precisely extensions of the form $\omega=\sum_l w_l|\psi_l\rangle\langle\psi_l|_{AB}\otimes|f_l\rangle\langle f_l|_L$, with normalized pure vectors, probability weights, arbitrary orthonormal flags, and $\sum_l w_l|\psi_l\rangle\langle\psi_l|=\rho_{AB}$. Let $E_F^{\rm bits}$ be Bennett's pure-state convex roof, computed with entropy in bits. Then
--
--   $$\min_{\omega\in K_2(\rho)} I_\omega(A:B\mid L)=2\ln(2)\,E_F^{\rm bits}(\rho).$$
--
--   The minimum is attained. This identifies the restricted $K_2$ optimization and does not identify unrestricted $K_0$ with Bennett formation.
-- source:
--   Entanglement of Distillation and Conditional Mutual Information, arXiv:quant-ph/0202144v2, PDF p. 4, §2, Eq.(9)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (9): attained K2 minimum is twice Bennett formation, in the same units.
Accepted formation is in bits, hence log 2 converts to nats. With corrected (4),
the factor is +2 because pure AB gives S(A)+S(B)=2 S(A). -/
theorem k2_minimum_formation {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Mat (A × B)) (hrho : IsDensityMatrix rho) :
    IsLeast (k2Scores rho)
      (2 * Real.log 2 * QAlgorithms.Papers.Independent.Information100.P08.formation rho) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P19
