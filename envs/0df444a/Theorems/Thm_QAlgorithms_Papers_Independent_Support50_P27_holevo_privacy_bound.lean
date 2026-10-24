-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P27_holevo_privacy_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P27.holevo_privacy_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:12:27.361016+00:00
-- url     : https://prove2.me/theorems/9371c095-3995-4862-a46c-20eca2cc0b06
-- title:
--   §5.2: small Holevo information bounds the hybrid privacy defect
-- statement:
--   Fix normalized finite conditional QKD output data, with public length probabilities $p_m$. For every length let $\mathcal F_m=\{2^{-m},\rho_{E,k,k}\}_k$ be the uniform diagonal ensemble and $\bar\rho_m$ its mean. Every conditional Eve state is a normalized density matrix, with arbitrary normalized representatives on null events. Define the hybrid states $\rho_{\mathrm{qi1}},\rho_{\mathrm{qi2}}$ by retaining the same equal uniform keys and using respectively $\rho_{E,k,k}$ and $\bar\rho_m$. Let
--
--   $$
--   H=\sum_mp_m\chi(\mathcal F_m),\qquad
--   \chi(\mathcal F_m)=S(\bar\rho_m)-2^{-m}\sum_kS(\rho_{E,k,k}),
--   \quad S(\rho)=-\operatorname{Tr}(\rho\log_2\rho).
--   $$
--
--   If $\mu'_2\ge0$ and $H\le\mu'_2$, then
--
--   $$
--   \lVert\rho_{\mathrm{qi1}}-\rho_{\mathrm{qi2}}\rVert_1
--   \le\sqrt{2\ln(2)H}\le\sqrt{2\ln(2)\mu'_2},
--   \qquad
--   \frac12\sum_mp_m2^{-m}\sum_k\lVert\rho_{E,k,k}-\bar\rho_m\rVert_1
--   \le\frac12\sqrt{2\ln(2)\mu'_2}.
--   $$
--
--   This controls the composable privacy defect without a length-dependent exponential factor. The trace norm is the full sum of singular values; the privacy defect has its separate factor one half.
-- source:
--   The Universal Composable Security of Quantum Key Distribution, arXiv:quant-ph/0409078v1, PDF p. 13, §5.2: small Holevo information implies composable privacy

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P27

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)

open QAlgorithms.Papers.Independent.Dependency50.P47 (cqMatrix)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.13--14, Section 5.2, Eq.(18) and the displayed bound after Eq.(19):
small weighted Holevo information bounds the FULL hybrid trace norm by
sqrt(2 ln(2) mu2). The Eq.(15) privacy defect is one half of this norm.
The accepted entropy has the standard minus sign; Appendix p.18 omits it.
Printed/used/why: Tr(rho log rho) / -Tr(rho log_2 rho) / required by Eq.(19)
and the nonnegative Holevo quantity of Section 5.2. No corrected theorem
constant is substituted. This sign clarification needs independent moderation. -/
theorem holevo_privacy_bound {L : ℕ} {E : Type} [Fintype E] [Nonempty E]
    (D : KeyData L E) (mu2 : ℝ) (hmu2 : 0 ≤ mu2)
    (hprivacy : diagonalHolevo D ≤ mu2) :
    traceNorm (firstHybrid D - secondHybrid D) ≤
      Real.sqrt (2 * Real.log 2 * diagonalHolevo D) ∧
    Real.sqrt (2 * Real.log 2 * diagonalHolevo D) ≤
      Real.sqrt (2 * Real.log 2 * mu2) ∧
    composablePrivacy D ≤ Real.sqrt (2 * Real.log 2 * mu2) / 2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P27

end
