-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_transpose_depolarizing_complement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.transpose_depolarizing_complement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:53:52.785843+00:00
-- url     : https://prove2.me/theorems/eaaae262-69e5-4275-b930-5aac2d48ecab
-- title:
--   Equations (17)–(18): extreme transpose-depolarizing complement
-- statement:
--   For integer $d\ge2$, let $\Phi_d(X)=(\operatorname{Tr}(X)I-X^T)/(d-1)$, with transpose in the fixed basis. It has the $d^2$ Kraus operators $K_{jk}=(|j\rangle\langle k|-|k\rangle\langle j|)/\sqrt{2(d-1)}$. Both $\Phi_d$ and the map
--
--   $$\Psi_d(X)=\frac{(I-F)(X\otimes I)(I-F)}{2(d-1)}$$
--
--   are channels, and the complement constructed from the displayed Kraus family equals $\Psi_d$ on every input operator. Here $F$ swaps the two $d$-dimensional factors. Thus this is an explicit common-dilation complement, with the full $d^2$ output retained.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 7, Equations (17)–(18): extreme transpose-depolarizing complement

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- Equations (17)–(18), PDF pp.7–8: all d^2 Kraus indices, fixed-basis
transpose, full factor 1/[2(d-1)], and equality on every operator. -/
theorem transpose_depolarizing_complement (d : ℕ) (hd : 2 ≤ d) :
    wernerHolevo d = krausApply (antisymmetricKraus d) ∧ IsChannel (wernerHolevo d) ∧
    IsChannel (antisymmetricComplement d) ∧ CPComplementary (wernerHolevo d) (antisymmetricComplement d) ∧
    (∀ rho, complementaryChannel (indexedKrausDilation (antisymmetricKraus d)) rho =
      antisymmetricComplement d rho) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
