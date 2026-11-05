-- Prove2me | Theorems.Thm_TwoWayCVQKD_twoWay_output_cms
-- name    : TwoWayCVQKD.twoWay_output_cms
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:52.220987+00:00
-- url     : https://prove2.me/theorems/06a54c62-4b90-4104-9047-745ea5e7c9f8
-- title:
--   Eqs. (47)–(53): the output covariance matrices of the two-way protocols
-- statement:
--   Consider the two-way model with Alice's modulation variance $\bar V\ge0$, Bob's EPR variance $V\ge1$, transmission $T\in[0,1]$ and EPR variance $W\ge1$ in each cloner. Then the covariance matrices computed from the sources are
--   $$
--   \mathbf V_B(\bar V,\bar V)=\begin{pmatrix}V\mathbf I&T\sqrt{V^2-1}\,\mathbf Z\\ T\sqrt{V^2-1}\,\mathbf Z&\mathbf\Lambda_B(\bar V,\bar V)\end{pmatrix},\qquad \mathbf V_E(\bar V,\bar V)=\begin{pmatrix} e_V\mathbf I & \varphi\mathbf Z & \mu'\mathbf I & \mathbf 0\\ \varphi\mathbf Z & W\mathbf I & \theta'\mathbf Z & \mathbf 0\\ \mu'\mathbf I & \theta'\mathbf Z & \mathbf\Lambda_E(\bar V,\bar V) & \varphi\mathbf Z\\ \mathbf 0 & \mathbf 0 & \varphi\mathbf Z & W\mathbf I\end{pmatrix},
--   $$
--   with $\mathbf\Lambda_B$, $\mathbf\Lambda_E$, $\mu'$, $\theta'$ as in Eqs. (49)–(52), and, for $K=B,E$,
--   $$
--   \mathbf V_{K|Q_A}=\mathbf V_K(0,\bar V),\qquad \mathbf V_{K|Q_A,P_A}=\mathbf V_K(0,0).
--   $$
--   These matrices are the input of every two-way rate.
--
--   **Formalization Note** The left-hand sides are computed from the sources and the two entangling cloners; the right-hand sides are the displays of the paper.
--
--   Differences from the source:
--   - encoding: an arbitrary quadruplet {V̄, V, W, T} → 0 ≤ V̄, 1 ≤ V, 0 ≤ T ≤ 1, 1 ≤ W; reason: the ranges of a variance, an EPR variance and a transmission
--   - encoding: beam splitter of transmission T, signs not printed → B = √T A + √(1−T) E and E′ = √T E − √(1−T) A; reason: this is the sign choice that gives μ of Eq. (19) and μ′, θ′ of Eq. (51); entropies do not depend on it
--   - encoding: the CM of Bob or Eve conditioned on Alice's classical variable → the Schur complement of the joint covariance; reason: this is the conditional covariance of jointly Gaussian variables, as in Eqs. (37)–(39)
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (47)–(53), pp.8–9

import Mathlib
import Definitions.Def_TwoWayCVQKD_twoWaySourceCov
import Definitions.Def_TwoWayCVQKD_twoWayBob
import Definitions.Def_TwoWayCVQKD_twoWayEve
import Definitions.Def_TwoWayCVQKD_condCov
import Definitions.Def_TwoWayCVQKD_aliceQ
import Definitions.Def_TwoWayCVQKD_twoWayBobCM
import Definitions.Def_TwoWayCVQKD_twoWayEveCM

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (47)–(53), pp.8–9: for an
arbitrary quadruplet `{Vbar, V, W, T}`, the model of the two-way protocols has Bob's covariance
matrix (47), Eve's (48), and the conditional matrices `V_K|Q_A = V_K(0, Vbar)`,
`V_K|Q_A,P_A = V_K(0, 0)` of (53) for `K = B, E`.

**Formalization Note** Conditional matrices are Schur complements. -/
theorem twoWay_output_cms (Vbar V T W : ℝ) (hVbar : 0 ≤ Vbar) (hV : 1 ≤ V) (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1) (hW : 1 ≤ W) :
    let Sg := twoWaySourceCov Vbar V W
    crossCov Sg (twoWayBob T) (twoWayBob T) = twoWayBobCM T W V Vbar Vbar ∧
    crossCov Sg (twoWayEve T) (twoWayEve T) = twoWayEveCM T W V Vbar Vbar ∧
    condCov Sg (twoWayBob T) aliceQ = twoWayBobCM T W V 0 Vbar ∧
    condCov Sg (twoWayBob T) aliceVar = twoWayBobCM T W V 0 0 ∧
    condCov Sg (twoWayEve T) aliceQ = twoWayEveCM T W V 0 Vbar ∧
    condCov Sg (twoWayEve T) aliceVar = twoWayEveCM T W V 0 0 := by sorry

end TwoWayCVQKD
