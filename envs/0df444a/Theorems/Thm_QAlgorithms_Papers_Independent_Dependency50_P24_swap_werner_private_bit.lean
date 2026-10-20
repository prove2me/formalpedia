-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_swap_werner_private_bit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.swap_werner_private_bit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:25:49.160014+00:00
-- url     : https://prove2.me/theorems/81aecc0f-edcf-4582-b4c2-1a42fc5fe471
-- title:
--   §IV-A: swap/Werner private bit
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   For an integer $d\ge2$, let $V|ij\rangle=|ji\rangle$, $X=V/d^2$, $\rho_s=(I+V)/(d^2+d)$, $\rho_a=(I-V)/(d^2-d)$, and $p=(1+1/d)/2$. Then $\gamma_V=\gamma_X$ is a private bit and
--
--   $$\gamma_V=p|\psi^+\rangle\langle\psi^+|\otimes\rho_s+(1-p)|\psi^-\rangle\langle\psi^-|\otimes\rho_a.$$
--
--   This is the swap/Werner example with normalized orthogonal flags.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 10, §IV-A: swap/Werner private bit

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF pp.10–11, Eqs.(48)–(50): normalized swap/Werner pbit, d>=2. -/
theorem swap_werner_private_bit (d : ℕ) (hd : 2 ≤ d) :
    IsPrivate (swapPrivate d) ∧
    swapPrivate d =
      ((1/2*(1+1/(d:ℝ)) : ℝ) : ℂ) • Matrix.kronecker (signedBell false false) (symmetricWerner d) +
      ((1-1/2*(1+1/(d:ℝ)) : ℝ) : ℂ) • Matrix.kronecker (signedBell false true) (antisymmetricWerner d) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
