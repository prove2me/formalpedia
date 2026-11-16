-- Prove2me | Theorems.Thm_PauliMixedness_Randomized_Supplement_adaptive_single_qubit_lower_bound
-- name    : PauliMixedness.Randomized.Supplement.adaptive_single_qubit_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:56:33.692389+00:00
-- url     : https://prove2.me/theorems/7bce869d-28af-4d96-9778-0c46b9f211eb
-- title:
--   Theorem 1.2 — adaptive single-qubit mixedness lower bound
-- statement:
--   There are absolute constants $c>0$, $N_0\ge1$ and $\varepsilon_0>0$ such that, for every $N\ge N_0$ and $0<\varepsilon\le\varepsilon_0$, every randomized adaptive single-copy tester using product single-qubit finite POVMs and $n$ copies satisfies
--
--   $$c(\sqrt{10})^N\le n\varepsilon^2 N^{1/4},$$
--
--   provided it accepts $\rho_{\rm mm}=I/2^N$ with probability at least $2/3$ and rejects every complex density matrix $\rho$ with $\|\rho-\rho_{\rm mm}\|_1\ge\varepsilon$ with probability at least $2/3$. The trace norm is unhalved. Measurement choices can depend on every previous outcome and an arbitrary measurable random seed; local POVMs have arbitrary finite outcome sets and need not be Pauli or projective. The constants precede the qubit count, accuracy, budget, seed space, law, and protocol.
--
--   This is the necessity counterpart to the randomized Pauli upper bound. The factor $N^{1/4}$ is the explicit polynomial in the proof on p.21.
--
--   Differences from the source:
--   - encoding: randomized adaptive single-copy finite POVMs and binary decision → arbitrary measurable seed law, history-dependent finite POVMs, finite Born recursion and an outcome-only [0,1] kernel; reason: all decision coins can be presampled independently of the state; outcome labels and measurable padded entries change no protocol instance
--   - generalization: Ω̃((√10)^N/ε²), i.e. n ≥ c(√10)^N/(ε² poly(N)) for an unspecified polynomial → c(√10)^N ≤ n ε² N^(1/4); reason: p.21 states the proof's explicit bound n = Ω((√10)^N/(N^(1/4)ε²)); the fixed polynomial N^(1/4) is one admissible poly(N), so the Lean statement implies the printed Ω̃ bound
--   - encoding: asymptotic lower bound → absolute c>0, N₀≥1 and ε₀>0 chosen before every instance, with the inequality multiplied out; reason: this records the uniform asymptotic range and avoids division by zero without excluding zero-copy protocols
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Theorem 1.2 p.3; proof §5.2 pp.20–21

import Definitions.Def_PauliMixedness_Randomized_Supplement_Adaptive

open MeasureTheory

namespace PauliMixedness.Randomized.Supplement

/-- Theorem 1.2 p.3; explicit N^(1/4) from p.21. Constants are uniform
in the qubit count, accuracy, copy count, seed space, law, and protocol. -/
theorem adaptive_single_qubit_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω]
          (μ : Measure Ω) [IsProbabilityMeasure μ] (A : AdaptiveProtocol N Ω),
          Uses A n {M | IsSingleQubit M} → AdaptiveSucceeds A μ n ε →
            c * Real.sqrt 10 ^ N ≤ (n : ℝ) * ε^2 * (N : ℝ) ^ (1 / 4 : ℝ) := by sorry

end PauliMixedness.Randomized.Supplement
