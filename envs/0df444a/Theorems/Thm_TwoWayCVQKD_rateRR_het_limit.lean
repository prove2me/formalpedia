-- Prove2me | Theorems.Thm_TwoWayCVQKD_rateRR_het_limit
-- name    : TwoWayCVQKD.rateRR_het_limit
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:10.308802+00:00
-- url     : https://prove2.me/theorems/b931e69f-5888-4e1c-a9d1-391cbd708601
-- title:
--   Eq. (46): asymptotic rate $R^{\blacktriangleleft}[Het]$
-- statement:
--   Fix a one-mode Gaussian attack with transmission $T\in(0,1)$ and EPR variance $W\ge1$, and let $R$ be the rate computed from the one-way model at modulation $V$. Then, as $V\to\infty$,
--   $$
--   R^{\blacktriangleleft}[Het]\ \longrightarrow\ \log\frac{2T}{e(1-T)(1+b_1)}+g\!\left(\frac{1-T+b_1}{T}\right)-g(W),
--   $$
--   where $g$ is the entropy function of Eq. (3), $b_1=(1-T)W+T$. The zero of this rate is the RR threshold of $Het$ in Fig. 3.
--
--   Differences from the source:
--   - encoding: the von Neumann entropy of a Gaussian density operator and the entropy of Eve's state conditioned on a classical variable → the covariance-matrix formulas: sum of g over the symplectic spectrum (Eq. (2)), Schur complement conditioning, one half of a log determinant for Shannon entropies; reason: the paper computes every entropy by exactly these formulas; Eq. (2) itself is its cited result [35]
--   - encoding: log in bits or nats → natural logarithm; reason: the paper allows either unit (p.6), and a rate in bits is the rate in nats divided by ln 2
--   - encoding: asymptotic value for V ≫ 1 → Tendsto as V → ∞ along atTop on ℝ; reason: the paper's limit of large modulation (V → +∞) in Figs. 2–3
--   - encoding: T ≠ 0, 1 → 0 < T and T < 1, with 1 ≤ W; reason: T is a beam-splitter transmission and W an EPR variance; W = 1 is pure loss
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (46), p.8

import Mathlib
import Definitions.Def_TwoWayCVQKD_rateRR
import Definitions.Def_TwoWayCVQKD_bVar
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49
open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)
open Filter
open scoped Topology

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (46), p.8: the asymptotic rate
`R◀[Het]` for `T ≠ 0, 1` and `V ≫ 1`.

**Formalization Note** The rate is computed from the model at each `V`; the limit is `V → ∞`. -/
theorem rateRR_het_limit (T W : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (hW : 1 ≤ W) :
    Tendsto (fun V : ℝ => rateRR .het V T W) atTop
      (𝓝 (Real.log (2 * T / (Real.exp 1 * (1 - T) * (1 + bVar T W 1))) +
        symplecticEntropy ((1 - T + bVar T W 1) / T) - symplecticEntropy W)) := by sorry

end TwoWayCVQKD
