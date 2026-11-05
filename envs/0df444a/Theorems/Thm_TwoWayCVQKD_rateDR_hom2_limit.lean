-- Prove2me | Theorems.Thm_TwoWayCVQKD_rateDR_hom2_limit
-- name    : TwoWayCVQKD.rateDR_hom2_limit
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:58.523091+00:00
-- url     : https://prove2.me/theorems/83c8b1ec-6ee2-4a1b-a0cb-d41a99346653
-- title:
--   Eqs. (61), (66): asymptotic rate $R^{\blacktriangleright}[Hom^2]$
-- statement:
--   Fix a one-mode Gaussian attack with transmission $T\in(0,1)$ and EPR variance $W\ge1$ in each cloner, and let $R$ be the rate computed from the two-way model at modulation $V$ with $\bar V=V-1$. Then, as $V\to\infty$,
--   $$
--   R^{\blacktriangleright}[Hom^2]\ \longrightarrow\ \frac12\log\frac{T}{(1-T)^2}-g(W),
--   $$
--   where $g$ is the entropy function of Eq. (3). The paper states this rate for $\otimes Hom^2$ in Eq. (61) and identifies the two in Eq. (66). The zero of this rate is the DR threshold of $Hom^2$ in Fig. 2.
--
--   Differences from the source:
--   - encoding: the von Neumann entropy of a Gaussian density operator and the entropy of Eve's state conditioned on a classical variable → the covariance-matrix formulas: sum of g over the symplectic spectrum (Eq. (2)), Schur complement conditioning, one half of a log determinant for Shannon entropies; reason: the paper computes every entropy by exactly these formulas; Eq. (2) itself is its cited result [35]
--   - encoding: log in bits or nats → natural logarithm; reason: the paper allows either unit (p.6), and a rate in bits is the rate in nats divided by ln 2
--   - encoding: asymptotic value for V ≫ 1 → Tendsto as V → ∞ along atTop on ℝ; reason: the paper's limit of large modulation (V → +∞) in Figs. 2–3
--   - encoding: T ≠ 0, 1 → 0 < T and T < 1, with 1 ≤ W; reason: T is a beam-splitter transmission and W an EPR variance; W = 1 is pure loss
--   - encoding: X_A = Q_A and X_B = Q_B (or the P quadrature) → the Q quadrature only; reason: the alternative quadrature gives the same rates by the Q/P symmetry of the model
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (61), (66), p.9

import Mathlib
import Definitions.Def_TwoWayCVQKD_rateDR
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49
open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)
open Filter
open scoped Topology

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (61), (66), p.9: the asymptotic rate
`R▶[Hom²]` for `T ≠ 0, 1` and `V ≫ 1`.

**Formalization Note** The rate is computed from the model at each `V`; the limit is `V → ∞`. -/
theorem rateDR_hom2_limit (T W : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (hW : 1 ≤ W) :
    Tendsto (fun V : ℝ => rateDR .hom2 V T W) atTop
      (𝓝 ((1 / 2) * Real.log (T / (1 - T) ^ 2) - symplecticEntropy W)) := by sorry

end TwoWayCVQKD
