-- Prove2me | Theorems.Thm_TwoWayCVQKD_oneWay_output_cms
-- name    : TwoWayCVQKD.oneWay_output_cms
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:17.448365+00:00
-- url     : https://prove2.me/theorems/da65c0da-b407-4814-9fe3-d0aa1455116b
-- title:
--   Eqs. (12)–(21): the output covariance matrices of the one-way protocols
-- statement:
--   Consider the one-way model at modulation $V\ge1$, transmission $T\in[0,1]$ and EPR variance $W\ge1$. Let $b_V=(1-T)W+TV$ and $e_V=(1-T)V+TW$, and let $\varphi$, $\mu$, $\theta$ be as in Eqs. (19)–(20). Then the covariance matrices computed from the sources are
--   $$
--   \mathbf V_B(V,V)=\mathbf\Delta(b_V,b_V),\qquad \mathbf V_E(V,V)=\begin{pmatrix}\mathbf\Delta[e_V,e_V]&\varphi\mathbf Z\\ \varphi\mathbf Z&W\mathbf I\end{pmatrix},\qquad \mathbf V_{EB}=\begin{pmatrix}\mathbf V_E&\mathbf F\\ \mathbf F^{\mathsf T}&\mathbf V_B\end{pmatrix},\quad \mathbf F:=\begin{pmatrix}\mu\mathbf I\\ \theta\mathbf Z\end{pmatrix},
--   $$
--   and, for $K=B,E$, the matrices conditioned on Alice's variable are
--   $$
--   \mathbf V_{K|Q_A}=\mathbf V_K(1,V),\qquad \mathbf V_{K|Q_A,P_A}=\mathbf V_K(1,1).
--   $$
--   The diagonal entries include the variances (12)–(15). These matrices are the input of every one-way rate.
--
--   **Formalization Note** The left-hand sides are computed from the sources and the entangling cloner; the right-hand sides are the displays of the paper.
--
--   Differences from the source:
--   - encoding: an arbitrary triplet {V, W, T} → 1 ≤ V, 0 ≤ T ≤ 1, 1 ≤ W; reason: the ranges of an EPR variance and a transmission; V = 1 is no modulation
--   - encoding: beam splitter of transmission T, signs not printed → B = √T A + √(1−T) E and E′ = √T E − √(1−T) A; reason: this is the sign choice that gives μ of Eq. (19) and μ′, θ′ of Eq. (51); entropies do not depend on it
--   - encoding: the CM of Bob or Eve conditioned on Alice's classical variable → the Schur complement of the joint covariance; reason: this is the conditional covariance of jointly Gaussian variables, as in Eqs. (37)–(39)
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (12)–(21), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_TwoWayCVQKD_oneWaySourceCov
import Definitions.Def_TwoWayCVQKD_oneWayBob
import Definitions.Def_TwoWayCVQKD_oneWayEve
import Definitions.Def_TwoWayCVQKD_condCov
import Definitions.Def_TwoWayCVQKD_aliceQ
import Definitions.Def_TwoWayCVQKD_oneWayBobCM
import Definitions.Def_TwoWayCVQKD_oneWayEveCM
import Definitions.Def_TwoWayCVQKD_muCoef
import Definitions.Def_TwoWayCVQKD_thetaCoef
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (12)–(21), p.7: for an
arbitrary triplet `{V, W, T}`, the model of the one-way protocols has Bob's covariance matrix (16),
Eve's (17), the joint matrix of Eve and Bob (18), and the conditional matrices
`V_K|Q_A = V_K(1, V)`, `V_K|Q_A,P_A = V_K(1, 1)` of (21) for `K = B, E`.

**Formalization Note** The joint family `x` lists modes `E', E'', B`. Conditional matrices are
Schur complements. -/
theorem oneWay_output_cms (V T W : ℝ) (hV : 1 ≤ V) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hW : 1 ≤ W) :
    let Sg := oneWaySourceCov V W
    let x : QuadratureIndex 3 → OneWaySrc → ℝ :=
      fun i => ![oneWayEve T (0, i.2), oneWayEve T (1, i.2), oneWayBob T (0, i.2)] i.1
    crossCov Sg (oneWayBob T) (oneWayBob T) = oneWayBobCM T W V V ∧
    crossCov Sg (oneWayEve T) (oneWayEve T) = oneWayEveCM T W V V ∧
    crossCov Sg x x = modeBlocks
      ![![eVar T W V • (1 : Matrix (Fin 2) (Fin 2) ℝ), phiCoef T W • zMat,
          muCoef T W V • (1 : Matrix (Fin 2) (Fin 2) ℝ)],
        ![phiCoef T W • zMat, W • (1 : Matrix (Fin 2) (Fin 2) ℝ), thetaCoef T W • zMat],
        ![muCoef T W V • (1 : Matrix (Fin 2) (Fin 2) ℝ), thetaCoef T W • zMat,
          bVar T W V • (1 : Matrix (Fin 2) (Fin 2) ℝ)]] ∧
    condCov Sg (oneWayBob T) aliceQ = oneWayBobCM T W 1 V ∧
    condCov Sg (oneWayBob T) aliceVar = oneWayBobCM T W 1 1 ∧
    condCov Sg (oneWayEve T) aliceQ = oneWayEveCM T W 1 V ∧
    condCov Sg (oneWayEve T) aliceVar = oneWayEveCM T W 1 1 := by sorry

end TwoWayCVQKD
