-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_trace_pairing
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.trace_pairing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:33:59.990577+00:00
-- url     : https://prove2.me/theorems/249f67df-da88-47ae-a628-ad6a9ad20c81
-- title:
--   Bilinear trace pairing of arbitrary symbols
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   For arbitrary operators $X,Y\in\mathcal C_{2n}$, use two anticommuting variable blocks $\theta,\mu$ and the left Berezin convention $D\theta=d\theta_{2n}\cdots d\theta_1$. Then
--   $$
--   \operatorname{Tr}(XY)=(-2)^n\int D\theta\,D\mu\ e^{\theta^T\mu}\omega(X,\theta)\omega(Y,\mu).
--   $$
--   There is no adjoint on $X$ and neither input needs a parity or Gaussianity restriction. The identity converts operator traces into finite Grassmann calculations.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 4, §IV, Eq.(15): trace pairing of arbitrary operator symbols

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Eq.(15): bilinear trace pairing, with no adjoint on X.
All theta and mu variables lie in a single Grassmann algebra. -/
theorem trace_pairing {n : ℕ} (s : CARSystem n) (X Y : Op (Qubits n)) :
    (X * Y).trace = (-2 : ℂ) ^ n *
      (grassMul
        (grassMul (grassExp (∑ a : Major n,
          grassMul (blockVars (2 * n) 2 0 a) (blockVars (2 * n) 2 1 a)))
          (grassSubst (majoranaSymbol s X) (blockVars (2 * n) 2 0)))
        (grassSubst (majoranaSymbol s Y) (blockVars (2 * n) 2 1))) Finset.univ := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
