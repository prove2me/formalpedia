-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_flower_private_bit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.flower_private_bit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:26:44.016831+00:00
-- url     : https://prove2.me/theorems/111a010d-0be2-43fa-a025-354e43c9b360
-- title:
--   §IV-A: flower private bit
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $\ell\ge0$ be an integer, $d=2^\ell$, $W=H^{\otimes\ell}$, $U=\sum_{ij}W_{ij}|ii\rangle\langle jj|$, and $\sigma=d^{-1}\sum_i|ii\rangle\langle ii|$. Put $X=U^T/d$ and let $\gamma_{\rm flower}$ be the block matrix (51), with diagonal shield blocks $\sigma/2$ and corners $X/2,X^\dagger/2$. Then
--
--   $$\|X\|_1=1,\quad\sqrt{XX^\dagger}=\sqrt{X^\dagger X}=\sigma,\quad\gamma_{\rm flower}=\gamma_X.$$
--
--   Consequently the flower state is a private bit, including the singleton-shield case $\ell=0$. The embedded $U$ is not a full-shield unitary.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 10, §IV-A: flower private bit

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

/-- PDF pp.10–11, Eqs.(51)–(53): flower pbit with d=2^ell, also ell=0.
The prose X=U^T omits 1/d; Eqs.(51)–(53) fix the normalization. -/
theorem flower_private_bit (ell : ℕ) :
    traceNorm (flowerOperator ell) = 1 ∧
    cfc Real.sqrt (flowerOperator ell * (flowerOperator ell)ᴴ) = flowerShield ell ∧
    cfc Real.sqrt ((flowerOperator ell)ᴴ * flowerOperator ell) = flowerShield ell ∧
    flowerPrivate ell = xForm (flowerOperator ell) ∧ IsPrivate (flowerPrivate ell) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
