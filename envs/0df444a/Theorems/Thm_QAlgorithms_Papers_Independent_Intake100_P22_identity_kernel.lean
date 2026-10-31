-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_identity_kernel
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.identity_kernel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:42:36.597835+00:00
-- url     : https://prove2.me/theorems/12d884e6-d798-4618-a4e6-2cbb4bdb581b
-- title:
--   Exact identity Gaussian integral kernel
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   The identity linear map has Gaussian-kernel parameters $C=1$, $A=D=0$, $B=I$. In particular, for every operator $X$,
--   $$
--   \omega(X,\theta)=\int e^{i\theta^T\eta+i\eta^T\mu}\omega(X,\mu)\,D\eta\,D\mu.
--   $$
--   All three variable blocks anticommute, and integration is left Berezin integration in the paper's order. No state, parity, or inverse-domain restriction is needed. This fixes the identity normalization for the map calculus.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 8, §VI, Eq.(39): identity Gaussian integral kernel

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Eq.(39): the identity kernel has C=1, A=D=0, B=I, and acts
on every operator without a parity, state, or invertibility restriction. -/
theorem identity_kernel {n : ℕ} (s : CARSystem n) :
    HasGrassmannKernel s id (homogeneousKernel 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
