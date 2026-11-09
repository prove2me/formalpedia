-- Prove2me | Theorems.Thm_PauliMixedness_Randomized_randomized_pauli_mixedness_tester
-- name    : PauliMixedness.Randomized.randomized_pauli_mixedness_tester
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:55:48.216489+00:00
-- url     : https://prove2.me/theorems/514c364e-3840-4116-ab0c-f1966a51ca28
-- title:
--   Theorem 1.1 — randomized nonadaptive Pauli mixedness tester
-- statement:
--   There exists an absolute $C>0$ such that for every integer $N\ge1$, every $\varepsilon>0$ and every $0<\delta\le1$, there are an integer copy count $n\ge0$ and a randomized nonadaptive product Pauli protocol $A$, fixed independently of the unknown state, satisfying
--
--   $$n\le\left\lceil C N^5\frac{(\sqrt{10})^N}{\varepsilon^2}\ln\frac1\delta\right\rceil.$$
--
--   On $\rho_{\rm mm}=I/2^N$, $A$ declares Maximally-Mixed with probability at least $1-\delta$. For every complex $2^N\times2^N$ density matrix $\rho$ with $\|\rho-\rho_{\rm mm}\|_1\ge\varepsilon$, it declares Not Maximally-Mixed with probability at least $1-\delta$. The norm is the unhalved Schatten 1 norm. Both probabilities include the presampled schedule, independent measurement outcomes and decision coins.
--
--   This is the full randomized Pauli upper bound, with the polynomial supported explicitly on p.16. No purity, reality, product structure, full rank or precomputed energy is assumed of the state.
--
--   Differences from the source:
--   - generalization: Algorithm 1 has $0<\varepsilon<1$ → the theorem covers every $\varepsilon>0$; reason: use threshold 1/2 for 1≤ε<2, increasing C by at most 16; for ε≥2 the far promise is empty and zero-copy acceptance suffices; restriction to 0<ε<1 recovers the source
--   - encoding: $\widetilde O$ hides polynomial factors in N → an absolute constant multiplying N^5 and an integer ceiling; reason: p.16 explicitly gives N^5; integer rounding does not remove any measurement or confidence clause
--   - encoding: a shared-seed nonadaptive measurement scheme and randomized binary decision → a PMF on complete Pauli schedules and an outcome-only [0,1] acceptance kernel; reason: finite schedules capture all shared randomness and decision coins without any state oracle; δ≥1/2 admits a zero-copy fair decision, preserving ln(1/δ) through δ=1
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Theorem 1.1 p.3, §1.1 p.2, proof pp.16–17

import Definitions.Def_PauliMixedness_Randomized_Protocol

namespace PauliMixedness.Randomized

/-- Theorem 1.1 p.3, with the explicit N^5 estimate of p.16. The all-positive
ε extension is declared in the metadata; the source algorithm uses ε ∈ (0,1). -/
theorem randomized_pauli_mixedness_tester :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 →
        ∃ (n : ℕ) (A : PauliProtocol N n),
          n ≤ ⌈C * (N : ℝ)^5 * Real.sqrt 10 ^ N / ε^2 * Real.log (1 / δ)⌉₊ ∧
          1 - δ ≤ acceptProbability A (maximallyMixed N) ∧
          ∀ ρ : Operator N, QAlgorithms.IsDensityMatrix ρ →
            ε ≤ QAlgorithms.traceNorm (ρ - maximallyMixed N) →
            1 - δ ≤ 1 - acceptProbability A ρ := by sorry

end PauliMixedness.Randomized
