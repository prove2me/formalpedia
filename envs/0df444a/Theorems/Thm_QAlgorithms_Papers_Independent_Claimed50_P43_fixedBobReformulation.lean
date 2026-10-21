-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_fixedBobReformulation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.fixedBobReformulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:22:49.07732+00:00
-- url     : https://prove2.me/theorems/eab65809-6ea2-4666-bf1b-a60408f410e2
-- title:
--   Attained common-marginal form of the one-shot assisted capacity
-- statement:
--   For a CPTP channel $\Phi:A\to A'$ between nonzero finite-dimensional spaces, let $B$ be a copy of $A$. Let $\Sigma_B$ consist of finite ensembles of density operators $\{\pi_i,S_{BA}^i\}$ for which all states have the same Bob marginal. That common density operator is allowed to vary between ensembles. In bits,
--
--   $$C_{\rm ea}^{(1)}(\Phi)=\max_{\{\pi_i,S_{BA}^i\}\in\Sigma_B}\left[H\!\left(\sum_i\pi_i(\operatorname{id}_B\otimes\Phi)(S_{BA}^i)\right)-\sum_i\pi_i H((\operatorname{id}_B\otimes\Phi)(S_{BA}^i))\right].$$
--
--   Both the common-marginal maximum and the original pure-resource/local-encoder maximum are attained. This removes explicit encoders without fixing one Bob state for the entire optimization.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 6, §III, equation (20): fixed-B-marginal reformulation

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.6, (20): equality and maximum attainment for the common-B formulation;
the marginal is chosen afresh inside each ensemble, not fixed for all candidates. -/
theorem fixedBobReformulation {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] [Nonempty A] [Nonempty C]
    (N : Superop A C) (hN : IsChannel N) :
    assistedOneShot N = sSup (commonBobValues N) ∧
    IsGreatest (commonBobValues N) (assistedOneShot N) ∧
    IsGreatest (assistedValues N) (assistedOneShot N) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
