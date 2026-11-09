-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_prefix_energy
-- name    : PrivateContinualCounting.Kraft.prefix_energy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:23.616395+00:00
-- url     : https://prove2.me/theorems/1fe38637-db65-40e8-869a-aaa6aeecd5bc
-- title:
--   Lemma 3.2 — prefix energy and the variance consequence
-- statement:
--   Let $g\in\mathcal G$ satisfy $K(g)$. Use the paper's canonical weight $f$, outer factor $h$, real scalar decoder $l=h/(1-z)$ and strategy $r=1/h$. For every integer $t\ge1$, let $E_t$ and $v_t$ be their coefficient energy and normalized variance. Then $p_th\in H^2$, the displayed spectral integrand is integrable, and the complete chain is
--   $$E_t=\sum_{j<t}l_j^2\le\|p_th\|_{H^2}^2=\int F_tf\,dm,
--   \qquad v_t\le\left(\int f^{-1}\,dm\right)\left(\int F_tf\,dm\right).$$
--   The equality, the energy inequality, the Parseval identity and the variance consequence are all retained. This links the exact canonical counter to the envelope estimate without assuming the latter.
--
--   Differences from the source:
--   - encoding: g defined on the real half-line [1,∞) → g is a function on ℝ with every envelope condition restricted to [1,∞); reason: Values below 1 are unused in all claims; monotonicity and doubling allow discontinuities.
--   - encoding: p_t h as a Hardy function and its norm → explicit finite coefficient convolution with H² membership and integrability as conclusions; reason: This prevents either the norm sum or the spectral integral from using a default value outside its domain. The source construction preamble is retained.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 8, PDF p. 10, Lemma 3.2 (prefix energy) and §3.3 preamble; Kisung Park, STOC 2027 submission #86 (October 2026), p. 20, PDF p. 22, Appendix C, proof of Lemma 3.2

import Definitions.Def_PrivateContinualCounting_Kraft_SpectralConstruction

open MeasureTheory

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Lemma 3.2: the entire energy/Parseval chain and its variance consequence. -/
theorem prefix_energy (g : ℝ → ℝ) (hg : IsEnvelope g) (hK : KraftCondition g)
    (t : ℕ) (ht : 0 < t) :
    (constructedData g).energy t =
      (∑ j ∈ Finset.range t, ((decoderCoeff g j).re) ^ 2) ∧
    prefixProductCoeff g t ∈ InfoShareH2.H2 ∧
    Integrable (fun θ => prefixKernel t θ * spectralWeight g θ) circleMeasure ∧
    (constructedData g).energy t ≤ hardyNormSq (prefixProductCoeff g t) ∧
    hardyNormSq (prefixProductCoeff g t) =
      (∫ θ, prefixKernel t θ * spectralWeight g θ ∂circleMeasure) ∧
    (constructedData g).variance t ≤
      (∫ θ, 1 / spectralWeight g θ ∂circleMeasure) *
      (∫ θ, prefixKernel t θ * spectralWeight g θ ∂circleMeasure) := by sorry

end PrivateContinualCounting.Kraft
