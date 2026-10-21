-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_transpose_complement_purity_transfer
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.transpose_complement_purity_transfer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:55:18.307526+00:00
-- url     : https://prove2.me/theorems/72d8c68c-2c79-4648-86a6-c6b0876ffc2e
-- title:
--   Inherited purity/additivity behavior of the antisymmetric complement
-- statement:
--   For $d\ge2$, let $\Psi_d$ be the antisymmetric complement in (18). Its inherited self-tensor properties are
--
--   $$\nu_p(\Psi_d\otimes\Psi_d)=\nu_p(\Psi_d)^2\quad(1\le p\le2),\qquad
--   \check H(\Psi_d\otimes\Psi_d)=2\check H(\Psi_d).$$
--
--   For $d>3$ there is a real $p_0>1$ such that every finite $p\ge p_0$ satisfies
--
--   $$\nu_p(\Psi_d\otimes\Psi_d)>\nu_p(\Psi_d)^2.$$
--
--   These are the same self-pair behaviors cited for the parent transpose-depolarizing channel and transferred to both complemented factors. No assertion about arbitrary second channels is added.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 8, Inherited purity/additivity behavior of the antisymmetric complement

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

/-- PDF pp.7–8: inherited SELF-tensor behavior from the cited results
for (17); no arbitrary-partner strengthening. -/
theorem transpose_complement_purity_transfer (d : ℕ) (hd : 2 ≤ d) :
    (∀ p : ℝ, 1 ≤ p → p ≤ 2 →
      Multiplicative (ENNReal.ofReal p) (antisymmetricComplement d) (antisymmetricComplement d)) ∧
    Additive (antisymmetricComplement d) (antisymmetricComplement d) ∧
    (3 < d → ∃ p0 : ℝ, 1 < p0 ∧ ∀ p : ℝ, p0 ≤ p →
      nu (ENNReal.ofReal p) (superopTensor (antisymmetricComplement d) (antisymmetricComplement d)) >
        nu (ENNReal.ofReal p) (antisymmetricComplement d) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
