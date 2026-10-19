-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P53_fidelityTensorMultiplicativity
-- name    : QAlgorithms.Papers.Independent.Information100.P53.fidelityTensorMultiplicativity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:05:36.159931+00:00
-- url     : https://prove2.me/theorems/1a336e57-a259-4454-8330-9792b1303b19
-- title:
--   Equation (3): multiplicativity of squared fidelity
-- statement:
--   Let $\rho_k,\psi_k$ be density matrices on $\mathbb C^{N_k}$ for $k=0,1$, with $N_k\ge1$. For squared Uhlmann fidelity $F(A,B)=(\operatorname{Tr}|\sqrt A\sqrt B|)^2$,
--
--   $$F(\rho_0\otimes\rho_1,\psi_0\otimes\psi_1)=F(\rho_0,\psi_0)F(\rho_1,\psi_1).$$
--
--   This background identity allows the paper to factor fidelities of product-state codewords into single-symbol fidelities.
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, PDF p. 3, Eq.(3)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.3, Eq.(3): the invoked background multiplicativity identity for
squared Uhlmann fidelity, with the tensor factors on positive finite dimensions. -/
theorem fidelityTensorMultiplicativity {N0 N1 : ℕ} (hN0 : 0 < N0) (hN1 : 0 < N1)
    (rho0 psi0 : Matrix (Fin N0) (Fin N0) ℂ)
    (rho1 psi1 : Matrix (Fin N1) (Fin N1) ℂ)
    (hrho0 : IsDensityMatrix rho0) (hpsi0 : IsDensityMatrix psi0)
    (hrho1 : IsDensityMatrix rho1) (hpsi1 : IsDensityMatrix psi1) :
    fidelity (Matrix.kronecker rho0 rho1) (Matrix.kronecker psi0 psi1) =
      fidelity rho0 psi0 * fidelity rho1 psi1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P53

end
