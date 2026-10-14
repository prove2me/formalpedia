-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_threshold_theorem
-- name    : QAlgorithms.GottesmanIntro.threshold_theorem
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:06:05.2172+00:00
-- url     : https://prove2.me/theorems/9b744429-db33-4613-b694-d6ddce7360ca
-- title:
--   Threshold theorem: below p_T, concatenated circuits simulate C to distance ε with polylog overhead
-- statement:
--   There exist an $[[n,1,2t+1]]$ code with fault-tolerant gadgets of a common depth (Definitions 2–5) and a threshold $p_T>0$ with the following property. For every $p$ with $0\le p<p_T$ there are constants $K>0$ and $c\in\mathbb N$ such that for every ideal circuit $C$ (Definition 6: preparation, $H$, $R_{\pi/8}$, CNOT, wait and measurement locations, no input) and every $\varepsilon>0$ there is a level $L$ for which the $L$-fold concatenated fault-tolerant simulation $C'=C^{(L)}$ satisfies
--
--   1. $\#\mathrm{qubits}(C')\le K\,\big(\log_2(2+|C|/\varepsilon)\big)^{c}\,\#\mathrm{qubits}(C)$ and $\#\mathrm{steps}(C')\le K\,\big(\log_2(2+|C|/\varepsilon)\big)^{c}\,\#\mathrm{steps}(C)$, where $|C|$ is the number of locations of $C$;
--   2. for every local stochastic error model on $C'$ (Definition 12) with error bounds $p_i\le p$, $p_i<1$,
--
--   $$d_{\mathrm{TV}}\big(\text{decoded output of } C',\ \text{output of } C\big)\le\varepsilon.$$
--
--   The output of $C'$ is decoded classically level by level. The threshold theorem shows that arbitrarily long quantum computations can be performed reliably with polylogarithmic overhead once the physical error rate is below a constant.
--
--   **Formalization Note** The fault-tolerant circuit is pinned to the concatenated circuit of the proof (p.42); an unconstrained circuit with free classical computation could sample the output of $C$ classically. $\mathrm{polylog}(x)$ is encoded as $K(\log_2(2+x))^c$, which is positive also for $x\le 1$.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 41, Theorem 10. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Definitions.Def_QAlgorithms_GottesmanIntro_Ch05b_Model
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro






/-- Gottesman intro p.41, Theorem 10 (threshold theorem): "There is a threshold error rate `p_T`.
Suppose we have a local stochastic error model with `p_i ≤ p < p_T`. Then for any ideal circuit
`C`, and any `ε > 0`, there exists a fault-tolerant circuit `C′` which, when it undergoes the
error model, produces an output which has statistical distance at most `ε` from the output of
`C`. `C′` has a number of qubits and a number of timesteps which are at most `polylog(|C|/ε)`
times bigger than the number of qubits and timesteps in `C`, where `|C|` is the number of
locations in `C`."

There are a fault-tolerant protocol `P` (an `[[n, 1, 2t + 1]]` code with gadgets of a common
depth) and a threshold `p_T > 0` such that for every `0 ≤ p < p_T` there are constants `K > 0` and
`c` with: for every ideal circuit `C` and every `ε > 0` there is a concatenation level `L` such
that `C′ = C^{(L)}` (the `L`-fold fault-tolerant simulation, p.42) has at most
`K (log₂(2 + |C|/ε))^c` times as many qubits and time steps as `C`, and for every local
stochastic error model on `C′` with bounds `p_i ≤ p` (`p_i < 1`, Def. 12) the decoded output
distribution of `C′` is within total variation distance `ε` of the output distribution of `C`. -/
theorem threshold_theorem :
    ∃ P : FTProtocol, P.IsFaultTolerant ∧ P.HasUniformDepth ∧
      ∃ pT : ℝ, 0 < pT ∧ ∀ p : ℝ, 0 ≤ p → p < pT →
        ∃ (K : ℝ) (c : ℕ), 0 < K ∧
          ∀ (N : ℕ) (C : LocCircuit N), C.IsIdealCircuit → ∀ ε : ℝ, 0 < ε →
            ∃ L : ℕ,
              ((concatCircuit P L C).numQubits : ℝ) ≤
                K * Real.logb 2 (2 + (C.size : ℝ) / ε) ^ c * (C.numQubits : ℝ) ∧
              ((concatCircuit P L C).numSteps : ℝ) ≤
                K * Real.logb 2 (2 + (C.size : ℝ) / ε) ^ c * (C.numSteps : ℝ) ∧
              ∀ (M : LocalStochasticModel (N * (P.n + P.A) ^ L)) (b : ℕ × ℕ → ℝ),
                (∀ ℓ ∈ (concatCircuit P L C).locs, b ℓ < 1) →
                (∀ ℓ ∈ (concatCircuit P L C).locs, b ℓ ≤ p) →
                IsLocalStochastic (concatCircuit P L C) M b →
                tvDist (pushDist (concatDecode P L C) (noisyOutDist (concatCircuit P L C) M))
                  C.idealOutDist ≤ ε := by
  sorry

end QAlgorithms.GottesmanIntro
