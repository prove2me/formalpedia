-- Prove2me | Theorems.Thm_PauliMixedness_Randomized_Supplement_adaptive_mic_lower_bound
-- name    : PauliMixedness.Randomized.Supplement.adaptive_mic_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:57:26.095561+00:00
-- url     : https://prove2.me/theorems/6686fe39-e168-4b78-bbac-6d90656bd1c2
-- title:
--   Theorem 1.3 — adaptive mixedness lower-bound framework
-- statement:
--   There are absolute constants $c>0$, $N_0\ge1$ and $\varepsilon_0>0$ such that for every $N\ge N_0$, $0<\varepsilon\le\varepsilon_0$, and every set $\mathcal M$ of finite POVMs on $N$ qubits, every randomized adaptive tester choosing from $\mathcal M$ and using $n$ copies satisfies
--
--   $$c4^N\le n\varepsilon^2\sqrt{o_{\mathcal M}t_{\mathcal M}}.$$
--
--   Here $o_{\mathcal M}=\sup_{M\in\mathcal M}\|L_M\|_{\rm op}$ and $t_{\mathcal M}=\sup_{M\in\mathcal M}\|L_M\|_1$ are separate suprema of the MIC's Schatten norms on the traceless Hilbert–Schmidt space. The premise is worst-case success at least $2/3$ on each of the null and all alternatives $\|\rho-I/2^N\|_1\ge\varepsilon$, using the unhalved trace norm and all complex density matrices. The same protocol must work for every alternative. Its seed has an arbitrary probability space and measurement choices depend on its classical history.
--
--   The framework relates measurement restrictions to adaptive copy complexity. It also covers empty or uninformative classes: the zero norm product then forces the nonexistence of any successful tester in the stated range.
--
--   Differences from the source:
--   - reading: the MIC norm domain is implicit → Schatten norms on the traceless Hilbert–Schmidt subspace; reason: §5.1 uses only traceless perturbation directions; removing the fixed identity eigenvalue gives the stronger reading specified in the brief
--   - encoding: randomized adaptive single-copy finite POVMs and binary decision → arbitrary measurable seed law, history-dependent finite POVMs, finite Born recursion and an outcome-only [0,1] kernel; reason: all decision coins can be presampled independently of the state; outcome labels and measurable padded entries change no protocol instance
--   - encoding: asymptotic lower bound → absolute c>0, N₀≥1 and ε₀>0 chosen before every instance, with the inequality multiplied out; reason: this records the uniform asymptotic range and avoids division by zero without excluding zero-copy protocols
--   - encoding: suprema of nonnegative MIC norms over the allowed class → real suprema with zero included; reason: all values are bounded by 1 and 2^N−1 respectively; adding zero changes no nonempty supremum and assigns norm zero to the empty class
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Theorem 1.3 p.3; Definition 3.1 p.10; proof §5.1 pp.18–20

import Definitions.Def_PauliMixedness_Randomized_Supplement_Adaptive
import Definitions.Def_PauliMixedness_Randomized_Supplement_MIC

open MeasureTheory

namespace PauliMixedness.Randomized.Supplement

/-- Theorem 1.3 p.3, with the traceless MIC-domain reading supported by
§5.1 pp.18-20. Each norm is separately maximized over the measurement class. -/
theorem adaptive_mic_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ (M : Set (FinitePOVM N)) (n : ℕ) (Ω : Type) [MeasurableSpace Ω]
          (μ : Measure Ω) [IsProbabilityMeasure μ] (A : AdaptiveProtocol N Ω),
          Uses A n M → AdaptiveSucceeds A μ n ε →
            c * (4 : ℝ)^N ≤ (n : ℝ) * ε^2 *
              Real.sqrt (classOpNorm M * classTraceNorm M) := by sorry

end PauliMixedness.Randomized.Supplement
