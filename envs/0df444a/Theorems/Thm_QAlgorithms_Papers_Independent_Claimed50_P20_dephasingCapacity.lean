-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_dephasingCapacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.dephasingCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:23:19.02614+00:00
-- url     : https://prove2.me/theorems/0aa544c5-e7c9-4be5-bd7a-c16110176af9
-- title:
--   Theorem 4: qubit dephasing dynamic capacity region
-- statement:
--   Write $r=(C,Q,E)\in\mathbb R^3$ for signed net classical, quantum and entanglement rates, with generation positive. The one-shot region $\mathcal C^{(1)}(\mathcal N)$ is the union over such pure ensembles of the simultaneous inequalities $C+2Q\le J_\sigma$, $Q+E\le K_\sigma$, and $C+Q+E\le L_\sigma$. The independent operational region $\mathcal C(\mathcal N)$ is the Euclidean closure of achievable net rates of the catalytic protocols of Section 3: local CPTP encoder and decoder, IID noisy uses, forward noiseless classical and quantum communication, consumed Bell entanglement, and generated classical correlation, entanglement transmission and Bell entanglement. Reliability is the full trace norm of the joint $M\widehat M RB_1S_AS_B$ output minus the product of its uniform classical-correlation target and its two Bell targets. Six finite nonnegative gross rates are fixed before the error and rounding tolerances; every sufficiently large positive blocklength has an appropriate code. Classical wires are dephased; no feedback is supplied.
--
--   Let $p\in[0,1]$ and let the qubit channel $\Delta_p(\rho)=(1-p)\rho+p\Delta(\rho)$ use complete computational-basis dephasing $\Delta$. Put
--
--   $$\gamma(\nu,p)=\frac12+\frac12\sqrt{1-16\frac p2\left(1-\frac p2\right)\nu(1-\nu)}.$$
--
--   Then
--
--   $$\mathcal C(\Delta_p)=\left\{(C,Q,E):\ \exists\nu\in[0,\tfrac12],\quad C+2Q\le1+H_2(\nu)-H_2(\gamma),\quad Q+E\le H_2(\nu)-H_2(\gamma),\quad C+Q+E\le1-H_2(\gamma)\right\}.$$
--
--   Here $H_2$ is binary entropy in bits and the same $\nu$ serves every inequality. The accepted dephasing primitive has coherence factor $1-p$. This describes all signed rates, including the identity and complete-dephasing endpoints.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 16, Theorem 4: qubit dephasing dynamic capacity region

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P20

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble PureEnsemble channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsHadamard)

open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 4, PDF p.16: complete-dephasing parameter p, a shared nu, and all signed octants. -/
theorem dephasingCapacity (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    operationalDynamicRegion (qubitDephasing (1 - p)) =
      {r | ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 1 / 2 ∧ rateConstraints (dephasingBounds p nu) r} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
