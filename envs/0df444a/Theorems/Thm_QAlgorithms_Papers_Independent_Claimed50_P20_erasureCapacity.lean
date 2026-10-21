-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_erasureCapacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.erasureCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:25:24.732747+00:00
-- url     : https://prove2.me/theorems/b42f34f2-a5ba-4f18-b68b-3bfc45bf7f25
-- title:
--   Theorem 5: qubit erasure dynamic capacity region
-- statement:
--   Write $r=(C,Q,E)\in\mathbb R^3$ for signed net classical, quantum and entanglement rates, with generation positive. The one-shot region $\mathcal C^{(1)}(\mathcal N)$ is the union over such pure ensembles of the simultaneous inequalities $C+2Q\le J_\sigma$, $Q+E\le K_\sigma$, and $C+Q+E\le L_\sigma$. The independent operational region $\mathcal C(\mathcal N)$ is the Euclidean closure of achievable net rates of the catalytic protocols of Section 3: local CPTP encoder and decoder, IID noisy uses, forward noiseless classical and quantum communication, consumed Bell entanglement, and generated classical correlation, entanglement transmission and Bell entanglement. Reliability is the full trace norm of the joint $M\widehat M RB_1S_AS_B$ output minus the product of its uniform classical-correlation target and its two Bell targets. Six finite nonnegative gross rates are fixed before the error and rounding tolerances; every sufficiently large positive blocklength has an appropriate code. Classical wires are dephased; no feedback is supplied.
--
--   Let $\epsilon\in[0,1]$ and let $\mathcal N_\epsilon$ be the qubit-to-qutrit erasure channel: $\mathcal N_\epsilon(X)=(1-\epsilon)X\oplus\epsilon\operatorname{Tr}(X)|e\rangle\langle e|$, where $|e\rangle$ is orthogonal to the qubit signal space. Then
--
--   $$\mathcal C(\mathcal N_\epsilon)=\left\{(C,Q,E):\ \exists p\in[0,\tfrac12],\quad C+2Q\le(1-\epsilon)(1+H_2(p)),\quad Q+E\le(1-2\epsilon)H_2(p),\quad C+Q+E\le1-\epsilon-\epsilon H_2(p)\right\}.$$
--
--   The same $p$ serves all three inequalities, and $H_2$ is binary entropy in bits. The antidegradable regime and both extreme erasure probabilities remain included. This is the exact operational region for a qubit input.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 18, Theorem 5: qubit erasure dynamic capacity region

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

/-- Theorem 5, PDF p.18: qubit-to-qutrit erasure, including epsilon>1/2 and endpoints. -/
theorem erasureCapacity (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) :
    operationalDynamicRegion (qubitErasure epsilon) =
      {r | ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 / 2 ∧ rateConstraints (erasureBounds epsilon p) r} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
