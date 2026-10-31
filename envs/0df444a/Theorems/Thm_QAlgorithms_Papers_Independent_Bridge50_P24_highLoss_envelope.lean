-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P24_highLoss_envelope
-- name    : QAlgorithms.Papers.Independent.Bridge50.P24.highLoss_envelope
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T15:35:12.375884+00:00
-- url     : https://prove2.me/theorems/3a0c1535-9711-4b9d-832d-8683f2314ee7
-- title:
--   First-order high-loss coefficient of the two-mode chain bound
-- statement:
--   Fix a natural number $n\geq 0$ of intermediate nodes, so the equally spaced chain has $n+1$ links. For intensity transmissivity $0<\eta<1$, define the displayed vanishing-error upper-bound curve in bits per optical pulse by
--
--   $$
--   U_n(\eta)=\frac{2}{n+1}\log_2\!\left(\frac{1+\eta}{1-\eta}\right).
--   $$
--
--   One pulse contains two polarization modes. As transmissivity tends to zero through $(0,1)$,
--
--   $$
--   \lim_{\eta\to 0^+}\frac{U_n(\eta)}{\eta}
--    =\frac{4}{(n+1)\ln 2}.
--   $$
--
--   This identifies the first-order coefficient of the source's upper-bound curve in the high-loss regime. It does not identify operational capacity or remove the finite-error correction for a protocol with fixed nonzero error.
-- source:
--   Fundamental rate-loss tradeoff for the quantum internet, arXiv:1601.02933v1, PDF p. 4, Unnumbered paragraph after Eq. (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P24

open Filter

open QAlgorithms.Papers.Independent.Gap20.P14 (rateLossCurve)

/-- arXiv:1601.02933v1, PDF p.4, unnumbered paragraph after Eq.(4):
for each fixed number n of intermediate nodes, the displayed upper-bound
curve has first-order coefficient 4 / ((n+1) ln 2) as intensity transmissivity
tends to zero through (0,1). This is a limit of the bound curve, not an
operational-capacity equality. No finite nonzero-error correction is dropped. -/
theorem highLoss_envelope (n : ℕ) :
    Tendsto (fun eta : ℝ => pulseRateEnvelope n eta / eta)
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
      (nhds (4 / (((n : ℝ) + 1) * Real.log 2))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P24

end
