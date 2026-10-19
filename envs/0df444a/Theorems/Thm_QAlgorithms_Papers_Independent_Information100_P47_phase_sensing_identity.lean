-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P47_phase_sensing_identity
-- name    : QAlgorithms.Papers.Independent.Information100.P47.phase_sensing_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:36:34.813131+00:00
-- url     : https://prove2.me/theorems/09dd3f22-6952-4428-a30b-1946e51ec8f0
-- title:
--   Phase-sensing Fisher information and three maximal coherence values
-- statement:
--   Let $0\le\nu\le1$ be fringe visibility and $\phi\in\mathbb R$ the phase. In the effective single-photon qubit model, put $E_+(\phi)=\frac12[I+\nu(\cos\phi\,\sigma_x+\sin\phi\,\sigma_y)]$ and $E_-(\phi)=I-E_+(\phi)$. On input $|+\rangle\langle+|$, the outcome probabilities are $p_\pm(\phi)=(1\pm\nu\cos\phi)/2$. Define Fisher information by summing $(\partial_\phi p_x)^2/p_x$ only over outcomes of strictly positive probability, and let $I_{\max}=\sup_\phi I(\phi)$. Let $D_1$ denote the maximum over normalized input states of classical total variation distance between Born distributions, $D_\diamond$ the measurement-channel diamond distance with factor $1/2$, and $D_\infty(A,B)=\frac12\sum_x\|A_x-B_x\|_{\mathrm{op}}$. Maximal coherence for each distance means minimum over complete diagonal POVMs and then maximum over all unitary conjugations. Then
--
--   $$I(\pi/2)=I_{\max}=\nu^2,\qquad C_{D_1}^{\max}(E(\phi))=C_{D_\diamond}^{\max}(E(\phi))=C_{D_\infty}^{\max}(E(\phi))=\frac\nu2,$$
--
--   and, for every phase,
--
--   $$I_{\max}=\left(2C_{D_1}^{\max}(E(\phi))\right)^2.$$
--
--   The Fisher maximum is attained. This identifies the phase sensitivity of the specified effective measurement with its maximal coherence. At deterministic phases with $\nu=1$, the positive-support convention sets the Fisher information to zero; it does not use a continuous extension or evaluate an undefined quotient.
--
--   For every regular phase with $p_+(\phi)p_-(\phi)>0$, the Fisher information is
--
--   $$I(\phi)=\frac{\nu^2\sin^2\phi}{1-\nu^2\cos^2\phi}.$$
--
--   For every phase, the corresponding sharpness also satisfies $S_{D_1}(E(\phi))=\nu/2$, so it equals the displayed maximal coherence.
-- source:
--   Maximal coherence of quantum measurement and the resource theory of sharpness, arXiv:2607.05847v1, PDF p. 8, §IV B, Eqs. (40)–(46)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Matrix

namespace QAlgorithms.Papers.Independent.Information100.P47

/-- PDF p.8, Eqs.(40)–(46): the maximum FI, all three coherence values, and their identity.
Printed Eq.(43) gives a quotient with no singular-phase convention.
Changed: assert that formula when both probabilities are positive, and use the
positive-support Fisher sum at singular phases. Why: at nu=1, phi=0 the printed
quotient has numerator and denominator zero. The maximum statement is unchanged.
The sharpness value in the paragraph preceding Eq.(45) is included explicitly;
Eq.(46) has the square of 2*C. -/
theorem phase_sensing_identity (nu : ℝ) (h0 : 0 ≤ nu) (h1 : nu ≤ 1) :
    IsGreatest (Set.range (fisherInformation nu)) (nu ^ 2) ∧
    fisherInformation nu (Real.pi / 2) = nu ^ 2 ∧
    maxFisherInformation nu = nu ^ 2 ∧
    ∀ phi : ℝ,
      (0 < phaseProbability nu phi 0 * phaseProbability nu phi 1 →
        fisherInformation nu phi =
          nu ^ 2 * Real.sin phi ^ 2 / (1 - nu ^ 2 * Real.cos phi ^ 2)) ∧
      sharpness (inducedDistance totalVariation) (phasePOVM nu phi) = ENNReal.ofReal (nu / 2) ∧
      maxCoherence (inducedDistance totalVariation) (phasePOVM nu phi) = ENNReal.ofReal (nu / 2) ∧
      maxCoherence diamondDistance (phasePOVM nu phi) = ENNReal.ofReal (nu / 2) ∧
      maxCoherence spectralDistance (phasePOVM nu phi) = ENNReal.ofReal (nu / 2) ∧
      maxFisherInformation nu =
        (2 * (maxCoherence (inducedDistance totalVariation) (phasePOVM nu phi)).toReal) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P47

end
