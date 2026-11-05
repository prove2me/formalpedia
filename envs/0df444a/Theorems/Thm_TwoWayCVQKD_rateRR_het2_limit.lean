-- Prove2me | Theorems.Thm_TwoWayCVQKD_rateRR_het2_limit
-- name    : TwoWayCVQKD.rateRR_het2_limit
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:30.651589+00:00
-- url     : https://prove2.me/theorems/14975914-d3c4-488e-b006-8679f4055d7e
-- title:
--   Eqs. (82)–(83): conditional spectrum and asymptotic rate $R^{\blacktriangleleft}[Het^2]$
-- statement:
--   Fix a one-mode Gaussian attack with transmission $T\in(0,1)$ and EPR variance $W\ge1$ in each cloner, and let $R$ be the rate computed from the two-way model at modulation $V$ with $\bar V=V-1$. Let $\boldsymbol\nu_{E|Q_B,P_B}$ be the symplectic spectrum of Eve's covariance matrix conditioned on Bob's variables $X_B=\{Q_B,P_B\}$. Then there are numbers $n_1,n_2,n_3$ with
--   $$
--   n_1n_2n_3=\frac{[1+T^3+(1-T)(1+T^2)W]W}{T(1+T)}
--   $$
--   such that, as $V\to\infty$, the spectrum behaves as $\{n_1,n_2,n_3,(1-T^2)V\}$, that is, its three smallest elements converge to $n_1,n_2,n_3$ and its largest element divided by $V$ converges to $1-T^2$, and
--   $$
--   R^{\blacktriangleleft}[Het^2]\ \longrightarrow\ \log\frac{2T(1+T)}{e(1-T)[1+T^2+(1-T^2)W]}+\sum_{i=1}^3g(n_i)-2g(W).
--   $$
--   The zero of this rate is the RR threshold of $Het^2$ in Fig. 3.
--
--   **Formalization Note** The paper states only the product of $n_1,n_2,n_3$, not each number, and this statement has the same strength. The Lean spectrum is sorted ascendingly.
--
--   Differences from the source:
--   - encoding: the von Neumann entropy of a Gaussian density operator and the entropy of Eve's state conditioned on a classical variable → the covariance-matrix formulas: sum of g over the symplectic spectrum (Eq. (2)), Schur complement conditioning, one half of a log determinant for Shannon entropies; reason: the paper computes every entropy by exactly these formulas; Eq. (2) itself is its cited result [35]
--   - encoding: log in bits or nats → natural logarithm; reason: the paper allows either unit (p.6), and a rate in bits is the rate in nats divided by ln 2
--   - encoding: asymptotic value for V ≫ 1 → Tendsto as V → ∞ along atTop on ℝ; reason: the paper's limit of large modulation (V → +∞) in Figs. 2–3
--   - encoding: T ≠ 0, 1 → 0 < T and T < 1, with 1 ≤ W; reason: T is a beam-splitter transmission and W an EPR variance; W = 1 is pure loss
--   - encoding: ν_E|Q_B,P_B → {n₁, n₂, n₃, (1−T²)V}, a growing spectrum element → the three smallest sorted eigenvalues converge to n₁, n₂, n₃ and the largest divided by V converges to 1 − T²; reason: this is the meaning of the paper's asymptotic spectrum; the fourth element diverges for T < 1
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (82)–(83), p.10

import Mathlib
import Definitions.Def_TwoWayCVQKD_rateRR
import Definitions.Def_TwoWayCVQKD_condCov
import Definitions.Def_TwoWayCVQKD_twoWaySourceCov
import Definitions.Def_TwoWayCVQKD_twoWayEve
import Definitions.Def_TwoWayCVQKD_twoWayHetBob
import Definitions.Def_GaussianGLOCC_sympSpec
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49
open GaussianGLOCC (sympSpec)
open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)
open Filter
open scoped Topology

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (82)–(83), p.10: for
`T ≠ 0, 1` and `V ≫ 1` the conditional spectrum is `ν_E|Q_B,P_B → {n₁, n₂, n₃, (1 - T²)V}`, where
`n₁n₂n₃ = [1 + T³ + (1 - T)(1 + T²)W]W / (T(1 + T))`, and it leads to the asymptotic rate (83).

**Formalization Note** The paper gives only the product of `n₁, n₂, n₃`, so the `nᵢ` are existentially
quantified, at that strength. `sympSpec` is sorted ascendingly: its first three entries converge to
the `nᵢ` and the last one, divided by `V`, converges to `1 - T²`. -/
theorem rateRR_het2_limit (T W : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (hW : 1 ≤ W) :
    ∃ n : Fin 3 → ℝ,
      n 0 * n 1 * n 2 = (1 + T ^ 3 + (1 - T) * (1 + T ^ 2) * W) * W / (T * (1 + T)) ∧
      (∀ i : Fin 3, Tendsto (fun V : ℝ => sympSpec
        (condCov (twoWaySourceCov (V - 1) V W) (twoWayEve T) (twoWayHetBob T)) i.castSucc)
          atTop (𝓝 (n i))) ∧
      Tendsto (fun V : ℝ => sympSpec
        (condCov (twoWaySourceCov (V - 1) V W) (twoWayEve T) (twoWayHetBob T)) 3 / V)
          atTop (𝓝 (1 - T ^ 2)) ∧
      Tendsto (fun V : ℝ => rateRR .het2 V T W) atTop
        (𝓝 (Real.log (2 * T * (1 + T) /
            (Real.exp 1 * (1 - T) * (1 + T ^ 2 + (1 - T ^ 2) * W))) +
          ∑ i, symplecticEntropy (n i) - 2 * symplecticEntropy W)) := by sorry

end TwoWayCVQKD
