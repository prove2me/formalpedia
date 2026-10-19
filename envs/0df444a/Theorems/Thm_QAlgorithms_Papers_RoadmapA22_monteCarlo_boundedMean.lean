-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA22_monteCarlo_boundedMean
-- name    : QAlgorithms.Papers.RoadmapA22.monteCarlo_boundedMean
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:26:59.973324+00:00
-- url     : https://prove2.me/theorems/c5375c4a-e7a2-46af-a928-d29fd844f32f
-- title:
--   Quantum Monte Carlo: bounded-output mean estimation
-- statement:
--   Let $A$ be the coherent unitary representation of a randomized or quantum computation on $n=h+k$ qubits, initially in $|0^n\rangle$, with no intermediate measurements and with access to its inverse. Measuring the last $k$ qubits gives a bit string $x$, whose output is the fixed value $\varphi(x)\in[0,1]$. The value-dependent flag rotation is supplied exactly; the source assumes that $\varphi$ is easily computable. Write $\mu=\mathbb E[v(A)]$.
--
--   Attach a fresh flag and prepare $|\psi\rangle$ by rotating it to $\sqrt{1-\varphi(x)}|0\rangle+\sqrt{\varphi(x)}|1\rangle$. Set $P=I\otimes|1\rangle\langle1|$, $U=2|\psi\rangle\langle\psi|-I$, and $V=I-2P$. For any positive integer $t$ and $0<\delta<1$, Algorithm 1 applies amplitude estimation independently $r(\delta)=2\lceil100\log(1/\delta)\rceil+1$ times and returns the median $\widetilde\mu$. One run uses uniform control on $\{0,\ldots,t-1\}$, controlled powers of $UV$, the inverse Fourier transform of dimension $t$, and the estimate $\sin^2(\pi j/t)$ for control outcome $j$.
--
--   There exist positive universal constants $C,K,D$, chosen before all sampler data and parameters, such that, with $L_\delta=\max\{1,\log(1/\delta)\}$,
--   $$
--   N_{\mathrm{copies}}\le K L_\delta,\qquad
--   N_U\le KtL_\delta,\qquad
--   \Pr\!\left[|\widetilde\mu-\mu|\le C\left(\frac{\sqrt\mu}{t}+\frac{1}{t^2}\right)\right]\ge1-\delta.
--   $$
--   Here the actual schedule consumes $r(\delta)$ fresh copies of $A|0^n\rangle$ and $r(\delta)(t-1)$ calls to $U$, counting controlled calls as uses.
--
--   For every $0<\varepsilon\le1$:
--   1. If $\mu>0$, there is a positive integer $t\le D/(\varepsilon\sqrt\mu)$ for which $\Pr[|\widetilde\mu-\mu|\le\varepsilon\mu]\ge1-\delta$.
--   2. There is a positive integer $t\le D/\varepsilon$ for which $\Pr[|\widetilde\mu-\mu|\le\varepsilon]\ge1-\delta$.
--
--   If $\mu=0$, the estimator returns zero with probability one for every positive integer $t$. The bounds hold for every coherent computation, including each instance of any oracle it uses. They quantify copies and reflections separately.
--
--   This is the bounded-output mean-estimation subroutine used by the paper's later Monte Carlo algorithms.
--
--   **Formalization Note** The selected result is Theorem 3 on PDF pages 8–9, rather than a later bounded-variance theorem. The printed reciprocal rates at $\varepsilon=0$ supply no finite exact-estimation claim; the reciprocal corollaries therefore use $0<\varepsilon\le1$. The all-confidence bound $L_\delta$ agrees with $O(\log(1/\delta))$ as $\delta$ tends to zero. The unspecified repetition coefficient is fixed to the odd representative above. The theorem asserts no gate-time bound for computing $\varphi$.
-- source:
--   Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, Theorem 3, §2.1 (continues on PDF p.9); Algorithm 1, PDF p. 8. https://arxiv.org/abs/1504.06987v3 . PDF SHA-256: 361ac540aeba94c89ad19bbd1c122c3a46e43b073522e155653dfb055e76c616.

import Definitions.Def_QAlgorithms_Defs_BoundedMeanEstimation
import Definitions.Def_QAlgorithms_Papers_RoadmapA22_Model
set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.RoadmapA22


/-- Quantum Monte Carlo mean estimation for bounded outputs: Montanaro,
arXiv:1504.06987v3, Theorem 3, PDF pp.8-9, with Algorithm 1 on p.8 and the
standing coherent-access model of Section 2 on p.7 (also Section 1.2, pp.3-4).

`S.A` acts on `n = S.h + S.k` qubits initialized in the all-zero state; the last
`S.k` qubits determine the output through `S.value`, which lies in `[0,1]` on
every basis outcome. The unitary representation has no intermediate measurements;
access includes its inverse. The frozen construction attaches a fresh flag by the
rotation with columns `(sqrt (1-value), sqrt value)` and
`(-sqrt value, sqrt (1-value))`. Thus `psi = boundedMeanState S`,
`U = meanEstimationReflection S = 2|psi><psi| - I`, and
`V = meanFlagReflection S = I - 2P`. The control schedule is independent of the
sampler and permits every positive integer `t`, including non-powers of two.

The first two bounds count fresh copies of `S.A|0^n>` and calls to `U`, including
controlled calls, from the frozen repetition list and controlled-power schedule.
The same universal constants work for every sampler and every internal oracle
instance. `max (1, log (1/delta))` states the resource bounds for all `0<delta<1`
and is equivalent to the printed logarithmic order as `delta` tends to zero.
The last two conjuncts are the relative- and additive-error corollaries, with
positive accuracy; only the relative reciprocal requires a positive mean.

The page prints `0 <= eps <= 1`, but its reciprocal bound gives no finite-query
exact-mean claim at `eps = 0`. We retain the meaningful `0 < eps <= 1` domain
and explicitly include the zero-mean behavior: the estimator outputs zero with
probability one. The source's 'easily computable' output function is used only
to implement the value-controlled rotation; this query/copy theorem assigns no
gate-time bound to that operation, and the frozen model supplies it exactly. -/
theorem monteCarlo_boundedMean :
    ∃ C K D : ℝ, 0 < C ∧ 0 < K ∧ 0 < D ∧
      ∀ (S : CoherentValueSampler) (delta : ℝ), 0 < delta → delta < 1 →
        (((boundedMeanCopyCount delta : ℕ) : ℝ) ≤
            K * max 1 (Real.log delta⁻¹) ∧
          ∀ (t : ℕ) (ht : 1 ≤ t),
            ((boundedMeanReflectionCount t delta : ℕ) : ℝ) ≤
                K * (t : ℝ) * max 1 (Real.log delta⁻¹) ∧
              1 - delta ≤ monteCarloSuccessProb S t ht delta
                (C * (Real.sqrt (samplerMean S) / (t : ℝ) + 1 / (t : ℝ) ^ 2)) ∧
              (samplerMean S = 0 → monteCarloSuccessProb S t ht delta 0 = 1)) ∧
        (∀ eps : ℝ, 0 < eps → eps ≤ 1 → 0 < samplerMean S →
          ∃ (t : ℕ) (ht : 1 ≤ t),
            (t : ℝ) ≤ D / (eps * Real.sqrt (samplerMean S)) ∧
              1 - delta ≤ monteCarloSuccessProb S t ht delta (eps * samplerMean S)) ∧
        (∀ eps : ℝ, 0 < eps → eps ≤ 1 →
          ∃ (t : ℕ) (ht : 1 ≤ t), (t : ℝ) ≤ D / eps ∧
            1 - delta ≤ monteCarloSuccessProb S t ht delta eps) := by sorry

end QAlgorithms.Papers.RoadmapA22
