-- Prove2me | Theorems.Thm_TwoWayCVQKD_rateDR_hom_limit
-- name    : TwoWayCVQKD.rateDR_hom_limit
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:43.744742+00:00
-- url     : https://prove2.me/theorems/d90053b5-d62c-484d-aa59-581a584fc899
-- title:
--   Eqs. (30), (33): asymptotic rate $R^{\blacktriangleright}[Hom]$
-- statement:
--   Fix a one-mode Gaussian attack with transmission $T\in(0,1)$ and EPR variance $W\ge1$, and let $R$ be the rate computed from the one-way model at modulation $V$. Then, as $V\to\infty$,
--   $$
--   R^{\blacktriangleright}[Hom]\ \longrightarrow\ \frac12\log\frac{Te_1}{(1-T)b_1}+g\!\left(\sqrt{\frac{Wb_1}{e_1}}\right)-g(W),
--   $$
--   where $g$ is the entropy function of Eq. (3), $b_1=(1-T)W+T$ and $e_1=(1-T)+TW$. The paper states this rate for $\otimes Hom$ in Eq. (30) and identifies the two in Eq. (33). The zero of this rate is the DR threshold of $Hom$ in Fig. 2.
--
--   Differences from the source:
--   - encoding: the von Neumann entropy of a Gaussian density operator and the entropy of Eve's state conditioned on a classical variable → the covariance-matrix formulas: sum of g over the symplectic spectrum (Eq. (2)), Schur complement conditioning, one half of a log determinant for Shannon entropies; reason: the paper computes every entropy by exactly these formulas; Eq. (2) itself is its cited result [35]
--   - encoding: log in bits or nats → natural logarithm; reason: the paper allows either unit (p.6), and a rate in bits is the rate in nats divided by ln 2
--   - encoding: asymptotic value for V ≫ 1 → Tendsto as V → ∞ along atTop on ℝ; reason: the paper's limit of large modulation (V → +∞) in Figs. 2–3
--   - encoding: T ≠ 0, 1 → 0 < T and T < 1, with 1 ≤ W; reason: T is a beam-splitter transmission and W an EPR variance; W = 1 is pure loss
--   - encoding: X_A = Q_A and X_B = Q_B (or the P quadrature) → the Q quadrature only; reason: the alternative quadrature gives the same rates by the Q/P symmetry of the model
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (30), (33), pp.7–8

import Mathlib
import Definitions.Def_TwoWayCVQKD_rateDR
import Definitions.Def_TwoWayCVQKD_bVar
import Definitions.Def_TwoWayCVQKD_eVar
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49
open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)
open Filter
open scoped Topology

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (30), (33), pp.7–8: the asymptotic rate
`R▶[Hom]` for `T ≠ 0, 1` and `V ≫ 1`.

**Formalization Note** The rate is computed from the model at each `V`; the limit is `V → ∞`. -/
theorem rateDR_hom_limit (T W : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (hW : 1 ≤ W) :
    Tendsto (fun V : ℝ => rateDR .hom V T W) atTop
      (𝓝 ((1 / 2) * Real.log (T * eVar T W 1 / ((1 - T) * bVar T W 1)) +
        symplecticEntropy (Real.sqrt (W * bVar T W 1 / eVar T W 1)) - symplecticEntropy W)) := by sorry

end TwoWayCVQKD
