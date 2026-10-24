-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P40_cat_asymptoticThreshold
-- name    : QAlgorithms.Papers.Independent.Support50.P40.cat_asymptoticThreshold
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:07:08.454332+00:00
-- url     : https://prove2.me/theorems/9f433d44-cb40-4f57-a445-f02aec14c25e
-- title:
--   Exact limiting threshold of the single-cat family
-- statement:
--   For each positive block size $p=m+1$, let $q_p(f)$ be the signed yield of the ordinary cat code computed from its exact joint probabilities, and define $\tau_p=\inf\{f\in[3/4,1]:q_p(f)>0\}$. These sets contain $1$.
--
--   There is a unique $f_\infty\in(3/4,1)$ such that, for $g_\infty=(1-f_\infty)/3$,
--
--   $$
--   \frac{(f_\infty-g_\infty)^2}{f_\infty+g_\infty}
--   =\sqrt{8g_\infty(f_\infty+g_\infty)},\qquad
--   \lim_{p\to\infty}\tau_p=f_\infty.
--   $$
--
--   The limit includes both even and odd block sizes. This equation specifies the threshold exactly; $.81808$ is only the paper's numerical approximation. No convergence rate or exact version of the informal partial contributions in Eqs. (40)–(41) is asserted.
-- source:
--   Quantum Channel Capacity of Very Noisy Channels, arXiv:quant-ph/9706061v3, PDF p. 18, Section V.A, Eq. (42): asymptotic cat-family threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF p.18, Eq.(42), Table I p.25, Fig.9 p.31: the high-fidelity
root is the limit of thresholds of the cat family, including both parities.
No exact decimal root, convergence rate, or intermediate asymptotic
identity from Eqs.(40)--(41) is asserted. -/
theorem cat_asymptoticThreshold :
    ∃ fstar : ℝ, (3 / 4 : ℝ) < fstar ∧ fstar < 1 ∧
      (fstar - noiseG fstar) ^ 2 / (fstar + noiseG fstar) =
        Real.sqrt (8 * noiseG fstar * (fstar + noiseG fstar)) ∧
      (∀ t : ℝ, (3 / 4 : ℝ) < t → t < 1 →
        (t - noiseG t) ^ 2 / (t + noiseG t) = Real.sqrt (8 * noiseG t * (t + noiseG t)) →
        t = fstar) ∧
      Filter.Tendsto catThreshold Filter.atTop (nhds fstar) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40
