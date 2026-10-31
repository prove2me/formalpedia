-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_visible_spectral_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.visible_spectral_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:36:15.112874+00:00
-- url     : https://prove2.me/theorems/388b0945-58df-401c-bbdf-cf2a8db8ecbf
-- title:
--   Lemma 4, (25)–(27): finite-block spectral converse
-- statement:
--   Let $\Xi$ be an arbitrary discrete label set and let $\mathcal H$ be a nonzero finite-dimensional complex Hilbert space. The source consists of normalized pure states $\rho_i$ and probabilities $p_i\ge0$ with $\sum_i p_i=1$; write $\rho_p=\sum_i p_i\rho_i$. Each memory space is finite and nonzero. Blind encoders and decoders are CPTP; a visible encoder maps labels to normalized density operators. A blind encoder is fixed before its input label.
--
--   For any visible code let $\epsilon=\sum_i p_i(1-\operatorname{Tr}(D(F(i))\rho_i))$. For every real $\lambda$, put $P_<=\{\rho_p-e^\lambda I<0\}$ and $P_\ge=\{\rho_p-e^\lambda I\ge0\}$, the orthogonal spectral projectors including equality only in $P_\ge$. Then
--
--   $$\epsilon+e^\lambda\dim\mathcal K\ge\operatorname{Tr}(\rho_pP_<),\qquad 1-\epsilon\le e^\lambda\dim\mathcal K+\operatorname{Tr}(\rho_pP_\ge).$$
--
--   Moreover, for every $s\ge1$, with $\psi(s)=\log\operatorname{Tr}\rho_p^s$,
--
--   $$1-\epsilon\le e^\lambda\dim\mathcal K+\exp((1-s)\lambda+\psi(s)).$$
--
--   This converse applies at any finite block by substituting the product ensemble, without a full-rank assumption.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 5, Lemma 4, (25)–(27): finite-block spectral converse

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- Lemma 4, PDF pp.5-6, (25)-(27): finite-block visible spectral converse,
including the equality threshold in the upper projector and every real lambda. -/
theorem visible_spectral_converse {L : Type*} {d : ℕ} (S : DiscretePureSource L d)
    (C : VisibleCode L (Fin d)) (lambda : ℝ) :
    let epsilon := averageLoss S.weight S.state (fun i => C.decode (C.encode i)) false
    epsilon + Real.exp lambda * C.memory ≥
      (S.average * thresholdProjection S.average lambda false).trace.re ∧
    1 - epsilon ≤ Real.exp lambda * C.memory +
      (S.average * thresholdProjection S.average lambda true).trace.re ∧
    ∀ s : ℝ, 1 ≤ s → 1 - epsilon ≤ Real.exp lambda * C.memory +
      Real.exp ((1 - s) * lambda + logPowerTrace S.average s) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
