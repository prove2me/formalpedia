-- Prove2me | Theorems.Thm_TwoWayCVQKD_superadditivity_security_thresholds
-- name    : TwoWayCVQKD.superadditivity_security_thresholds
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:52:32.292009+00:00
-- url     : https://prove2.me/theorems/5de7812e-d078-4955-a59f-210655515559
-- title:
--   p.4: two-way security thresholds beat one-way ones, the only exception being $Hom^2$ in DR for $T>T_c\simeq 0.86$
-- statement:
--   Consider the individual protocols $Hom$, $Het$ (one-way) and $Hom^2$, $Het^2$ (two-way) under a one-mode Gaussian attack with transmission $T\in(0,1)$ and EPR variance $W\ge1$, where the two paths of a two-way protocol are attacked by independent cloners with the same $(T,W)$, and let $R^{\blacktriangleright}_\infty$, $R^{\blacktriangleleft}_\infty$ be the rates in the limit of large modulation. The security thresholds are the boundaries $R=0$. Then:
--
--   1. for all $T\in(0,1)$ and $W\ge1$, each of the eight rates $R^{\blacktriangleright}$, $R^{\blacktriangleleft}$ of the four protocols converges as $V\to\infty$;
--   2. for every $T\in(0,1)$, the two-way thresholds improve on the one-way thresholds in reverse reconciliation, for $Hom^2$ over $Hom$ and for $Het^2$ over $Het$, and in direct reconciliation for $Het^2$ over $Het$;
--   3. there is a critical transmission $T_c$ with $0.855<T_c<0.865$ such that, in direct reconciliation, $Hom^2$ improves on $Hom$ for $T<T_c$ and $Hom$ improves on $Hom^2$ for $T>T_c$.
--
--   Here $r_2$ improves on $r_1$ means that $r_2(W)>0$ wherever $r_1(W)\ge0$, and that if $r_2$ is ever positive then $r_1(W)<0<r_2(W)$ for some $W\ge1$.
--
--   This is the superadditivity of the security thresholds: two channel uses that are too noisy for one-way QKD can be combined into a secure two-way QKD, as long as the channel is memoryless.
--
--   **Formalization Note** At a $T$ where neither scheme is ever secure, both thresholds vanish and the comparison holds trivially, matching the vanishing thresholds at low $T$ in Fig. 2.
--
--   Differences from the source:
--   - encoding: the von Neumann entropy of a Gaussian density operator and the entropy of Eve's state conditioned on a classical variable → the covariance-matrix formulas: sum of g over the symplectic spectrum (Eq. (2)), Schur complement conditioning, one half of a log determinant for Shannon entropies; reason: the paper computes every entropy by exactly these formulas; Eq. (2) itself is its cited result [35]
--   - encoding: log in bits or nats → natural logarithm; reason: the paper allows either unit (p.6), and a rate in bits is the rate in nats divided by ln 2
--   - reading: the security thresholds are improved almost everywhere (the only exception being Hom² for T > T_c ≃ 0.86 in DR) → Improves for RR Hom/Hom², RR Het/Het² and DR Het/Het² at every T ∈ (0, 1); Improves for DR Hom/Hom² below T_c and its reverse above T_c; reason: 'almost everywhere' refers to the one stated exception; the reverse above T_c is the stronger reading of an exception, and it is what Figs. 2–3 show
--   - reading: T_c ≃ 0.86 → 0.855 < T_c < 0.865; reason: the printed precision of the value
--   - reading: a security threshold N(T) improved (the boundary R = 0 moves to larger noise) → Improves r₁ r₂: r₂ > 0 wherever r₁ ≥ 0 (W ≥ 1), and r₁ < 0 < r₂ at some W ≥ 1 whenever r₂ is ever positive; holds trivially at a T where neither rate is ever positive; reason: it compares the thresholds without defining them as a supremum, so no monotonicity in W is assumed; where both thresholds vanish (low T in Fig. 2) the paper's comparison is trivial too
--   - encoding: thresholds N(T) of the excess noise N = (W − 1)(1 − T)/T → comparison on the axis W ≥ 1; reason: at fixed T ∈ (0, 1), W ↦ N is an increasing bijection of [1, ∞) onto [0, ∞)
--   - encoding: limit of large modulation V → +∞ of Figs. 2–3 → convergence concluded as clause 1, then limUnder; reason: the limit is proved to exist, so no default value enters
--   - encoding: X_A = Q_A and X_B = Q_B (or the P quadrature) → the Q quadrature only; reason: the alternative quadrature gives the same rates by the Q/P symmetry of the model
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.4, 'From one-way to two-way protocols', with the thresholds of Figs. 2–3 (pp.2–3)

import Mathlib
import Definitions.Def_TwoWayCVQKD_asymRateDR
import Definitions.Def_TwoWayCVQKD_asymRateRR
import Definitions.Def_TwoWayCVQKD_Improves
open Filter
open scoped Topology

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.4, with the thresholds of
Figs. 2–3: "By comparing Hom² with Hom and Het² with Het, one sees that the security thresholds are
improved almost everywhere (the only exception being Hom² for T > T_c ≃ 0.86 in DR). Such a
superadditive behavior is the central result of this work."

**Formalization Note** For `T ∈ (0, 1)` and `W ≥ 1`, all eight rates converge as `V → ∞`. Then the
thresholds of the asymptotic rates compare by `Improves`, in RR for `Hom`, `Het` and in DR for
`Het` at every `T`, and in DR for `Hom` below a critical value `Tc`. Above `Tc` the comparison is
reversed. `Tc` is read at its printed precision: `0.855 < Tc < 0.865`. -/
theorem superadditivity_security_thresholds :
    (∀ (p : Protocol) (T W : ℝ), 0 < T → T < 1 → 1 ≤ W →
      (∃ r, Tendsto (fun V : ℝ => rateDR p V T W) atTop (𝓝 r)) ∧
      (∃ r, Tendsto (fun V : ℝ => rateRR p V T W) atTop (𝓝 r))) ∧
    (∀ T : ℝ, 0 < T → T < 1 →
      Improves (asymRateRR .hom T) (asymRateRR .hom2 T) ∧
      Improves (asymRateRR .het T) (asymRateRR .het2 T) ∧
      Improves (asymRateDR .het T) (asymRateDR .het2 T)) ∧
    ∃ Tc : ℝ, 0.855 < Tc ∧ Tc < 0.865 ∧
      (∀ T : ℝ, 0 < T → T < Tc → Improves (asymRateDR .hom T) (asymRateDR .hom2 T)) ∧
      (∀ T : ℝ, Tc < T → T < 1 → Improves (asymRateDR .hom2 T) (asymRateDR .hom T)) := by sorry

end TwoWayCVQKD
