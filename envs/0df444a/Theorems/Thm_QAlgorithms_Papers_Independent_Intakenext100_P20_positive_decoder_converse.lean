-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_positive_decoder_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.positive_decoder_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:38:52.62861+00:00
-- url     : https://prove2.me/theorems/f90d3890-45b9-4e0d-883e-e5b21468995d
-- title:
--   Remark 5, (34): positive-map decoder converse
-- statement:
--   Let $\Xi$ be an arbitrary discrete label set, let $\rho_i$ be normalized pure source states on a nonzero finite-dimensional complex space $\mathcal H$, and let $p_i\ge0$ sum to one. Write $\rho_p=\sum_i p_i\rho_i$. Let $\mathcal K$ be finite and nonzero, $F:\Xi\to\mathcal S(\mathcal K)$ any visible encoder, and $D$ a positive, trace-preserving complex-linear decoder. For $\epsilon=\sum_i p_i(1-\operatorname{Tr}(D(F(i))\rho_i))$ and every real $\lambda$,
--
--   $$1-\epsilon\le2e^\lambda\dim\mathcal K+2\operatorname{Tr}\bigl(\rho_p\{\rho_p-e^\lambda I\ge0\}\bigr).$$
--
--   Complete positivity is not required for this factor-two spectral converse.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 6, Remark 5, (34): positive-map decoder converse

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

/-- Remark 5, PDF p.6, (34), Appendix D p.11: positivity suffices when
both right-hand terms are multiplied by two; trace preservation is retained. -/
theorem positive_decoder_converse {L : Type*} {d m : ℕ} (S : DiscretePureSource L d)
    (hm : 0 < m) (F : L → Matrix (Fin m) (Fin m) ℂ)
    (hF : ∀ i, IsDensityMatrix (F i))
    (D : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hD : IsPositiveTracePreserving D) (lambda : ℝ) :
    1 - averageLoss S.weight S.state (fun i => D (F i)) false ≤
      2 * Real.exp lambda * m +
      2 * (S.average * thresholdProjection S.average lambda true).trace.re := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
