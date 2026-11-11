-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_pilot_concentration
-- name    : SingleCopyMoments.Adaptive.pilot_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:47:03.034435+00:00
-- url     : https://prove2.me/theorems/7b031dbb-4671-45f7-8295-9721fc51b7be
-- title:
--   Lemma 21 — Concentration of the pilot matrix
-- statement:
--   Fix a $d$-dimensional state $\rho$, $x\in[0,1]$ and $n\ge1$ independent pilot trials from the specified Haar/covariant mixture. With $S_x,B_x,H_x$ defined above, uniformly over these choices,
--
--   $$\mathbb E B_x=H_x,\qquad\mathbb E\|B_x-H_x\|_{HS}^2\le\frac{24}n,\qquad\mathbb E|\operatorname{Tr}(B_x-H_x)|^2\le\frac{24}n.$$
--
--   For every real threshold $L>2n/d$,
--
--   $$\Pr\{\|S_x\|_{op}\ge L\}\le d\left(\frac{2en}{Ld}\right)^L.$$
--
--   The law is a probability measure, and all displayed expectations are integrable. These are joint expectations over the independent mixture trials with the input state fixed. The identities control both matrix approximation and its normalization.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 21, (6.2)–(6.3), printed p. 22 (PDF p. 24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Pilot

open scoped Matrix.Norms.L2Operator

open MeasureTheory
open scoped ENNReal

namespace SingleCopyMoments.Adaptive

/-- Lemma 21, printed pp.22–23 (PDF pp.24–25), all of (6.2) and (6.3). -/
theorem pilot_concentration (d n : ℕ) (hd : 0 < d) (hn : 1 ≤ n)
    (H : HaarBasis d) (ρ : State d) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (pilotLaw H ρ x n) ∧
    Integrable (pilotB ρ x) (pilotLaw H ρ x n) ∧
    Integrable (fun v => hsSq (pilotB ρ x v - pilotH ρ x)) (pilotLaw H ρ x n) ∧
    Integrable (fun v => ‖(pilotB ρ x v - pilotH ρ x).trace‖ ^ 2) (pilotLaw H ρ x n) ∧
    (∫ v, pilotB ρ x v ∂pilotLaw H ρ x n) = pilotH ρ x ∧
    (∫ v, hsSq (pilotB ρ x v - pilotH ρ x) ∂pilotLaw H ρ x n) ≤ 24/(n : ℝ) ∧
    (∫ v, ‖(pilotB ρ x v - pilotH ρ x).trace‖ ^ 2 ∂pilotLaw H ρ x n) ≤ 24/(n : ℝ) ∧
    ∀ L : ℝ, 2*(n : ℝ)/(d : ℝ) < L →
      (pilotLaw H ρ x n) {v | L ≤ opNorm (pilotS v)} ≤
        ENNReal.ofReal ((d : ℝ) * (2 * Real.exp 1 * n / (L*d)) ^ L) := by sorry

end SingleCopyMoments.Adaptive
