-- Prove2me | Theorems.Thm_TargetedSamplers_theorem_4_2
-- name    : TargetedSamplers.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:23.820827+00:00
-- url     : https://prove2.me/theorems/453a9a22-46be-467a-8bdd-f7bc0fb25fbd
-- title:
--   Theorem 4.2 — overhead-free error reduction for quantified derandomization (corrected: prBPTIME error is Q/2^T)
-- statement:
--   There are universal constants $c_0,c_1,c_2>0$ such that for every $\epsilon>0$ and every time-constructible monotone $T:\mathbb N\to\mathbb N$,
--   $$\mathrm{prBPTIME}_{2^{(1-\epsilon)T}}[T]\subseteq\mathrm{prBPTC}_{2^{C^{1-c_2\epsilon^3}}}\big[\lceil T^{1+c_1\epsilon}\rceil,\ C=\lceil T^{1+c_0\epsilon^2}\rceil\big].$$
--   An algorithm with $T$ coins, time $T$ and error $2^{-\epsilon T}$ becomes one with $C=T^{1+O(\epsilon^2)}$ coins, time $T^{1+O(\epsilon)}$ and at most $2^{C^{1-O(\epsilon^3)}}$ bad coin strings.
--
--   This is the first step of the proof of Theorem 4.30.
--
--   Differences from the source:
--   - reading: the three O(·) → universal constants c₀, c₁, c₂ > 0 chosen before ϵ and T; reason: with c₂ = 0 the target class would allow 2^C bad coin strings and be trivial
--   - encoding: T^{1+O(ϵ)}, C^{1−O(ϵ³)}, T^{1+O(ϵ²)} → real powers, rounded up to naturals where a natural is needed; reason: the page leaves rounding implicit
--   - generalization: monotone increasing T → Monotone T (non-decreasing); reason: the proof uses only monotonicity; every strictly increasing T is an instance
--   - correction: prBPTIME_Q[T]: "error probability δ = Q/T" (Theorem 1.6, p.5) → error at most Q(T(n))/2^{T(n)}; reason: counterexample: with Q = 2^{(1−ϵ)T}, Q/T ≥ 1 for large T, so the printed class contains every promise problem, e.g. the halting problem, which no bounded-error algorithm decides; Definition 4.1 and §4.1 use Q/2^T
--   - reading: "runs in time t" on an unspecified RAM → time at most budget = K·(t+1)·(log₂(n+t+2)+1)^k on the log-cost RAM; reason: the paper fixes no cost model; the log-cost RAM differs from a word RAM by polylogarithmic factors
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.2, p.20 (pdf p.22)

import Mathlib
import Definitions.Def_TargetedSamplers_InPrBPTC
import Definitions.Def_TargetedSamplers_TimeConstructible

namespace TargetedSamplers

/-- Theorem 4.2 (overhead-free error-reduction for quantified derandomization) (Chen, Doron, Ebtehaj,
Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, p.20). For every `ϵ > 0`
and time-constructible monotone increasing `T : ℕ → ℕ`,
`prBPTIME_{2^{(1−ϵ)T}}[T] ⊆ prBPTC_{2^{C^{1−O(ϵ³)}}}[T^{1+O(ϵ)}, C = T^{1+O(ϵ²)}]`.

**Formalization Note** The three `O(·)` are universal constants `c₀, c₁, c₂ > 0` chosen before `ϵ`
and `T` (with `c₂ = 0` the target class would allow `Q = 2^C` and be trivial). Real powers are
rounded up; "increasing" is `Monotone`. Time in the classes is `budget`. -/
theorem theorem_4_2 : ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
    ∀ ϵ : ℝ, 0 < ϵ → ∀ T : ℕ → ℕ, TimeConstructible T → Monotone T →
    ∀ L : KarpLiptonOM.PromiseProblem, InPrBPTIME (fun c => (2 : ℝ) ^ ((1 - ϵ) * c)) T L →
      InPrBPTC (fun c => (2 : ℝ) ^ ((c : ℝ) ^ (1 - c₂ * ϵ ^ 3)))
        (fun n => ⌈(T n : ℝ) ^ (1 + c₁ * ϵ)⌉₊) (fun n => ⌈(T n : ℝ) ^ (1 + c₀ * ϵ ^ 2)⌉₊) L := by sorry

end TargetedSamplers
