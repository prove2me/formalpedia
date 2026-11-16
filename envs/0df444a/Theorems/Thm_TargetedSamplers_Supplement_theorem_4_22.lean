-- Prove2me | Theorems.Thm_TargetedSamplers_Supplement_theorem_4_22
-- name    : TargetedSamplers.Supplement.theorem_4_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:14:46.533777+00:00
-- url     : https://prove2.me/theorems/6fb7252f-89cd-412f-81e5-c0424a69e2cd
-- title:
--   Theorem 4.22 — overhead-free quantified derandomization from SVN circuit lower bounds
-- statement:
--   For every $\epsilon>0$ there is a constant $\alpha>0$ such that the following holds. Assume that there is a language $L\in\mathrm{DTIME}[2^n]$ whose truth table on length $n$ can be printed in time $2^{(1+\alpha)n}$ for every $n$, but which cannot be computed by SVN circuits of size $2^{(1-\alpha/4)n}$. Then, for $B(T)=2^{(1-\epsilon)T}$ and every time-constructible increasing $T:\mathbb N\to\mathbb N$,
--   $$\mathrm{prBPTIME}_{B}[T]\subseteq\mathrm{prDTIME}\big[T^{1+c\epsilon}\big],$$
--   where $c>0$ is a universal constant.
--
--   Here $\mathrm{prBPTIME}_B[T]$ is the class of promise problems decided in time $T$ with $T$ coins and error at most $B(T)/2^T=2^{-\epsilon T}$. The theorem derandomizes algorithms of exponentially small error with almost no time overhead from a non-uniform hardness assumption; Theorem 4.30, the goal, replaces it by a uniform one.
--
--   **Formalization Note** The constant $c$ of $O(\epsilon)$ is chosen before $\epsilon$; $\alpha$ depends on $\epsilon$. Classes are the base mission's `InPrBPTIME` and `InPrDTIME`; time is `budget`.
--
--   Differences from the source:
--   - reading: T unquantified → every time-constructible monotone T; reason: the proof applies Theorem 4.2 with this T, and Theorem 4.2 states exactly this hypothesis
--   - reading: L cannot be computed by SVN circuits of size 2^{(1−α/4)n} → for all sufficiently large n; reason: almost-everywhere hardness, as in [CT21b]; at n = 0 a gate-free SVN circuit computes every language, so 'for every n' would be unsatisfiable
--   - encoding: O(ϵ); a constant α → c·ϵ with c > 0 universal, chosen before ϵ; α > 0 depending on ϵ; reason: standard reading of the constants; the proof takes α = Θ(ϵ³)
--   - encoding: prBPTIME_B[T] → the base InPrBPTIME: T coins, error B(T)/2^T; reason: the published base convention, as in the goal
--   - encoding: size of an SVN circuit → number of fan-in-2 AND/OR and NOT gates; reason: standard; the paper does not define SVN circuits
--   - encoding: time bounds → the base mission's budget (constant and polylogarithmic factors); real powers rounded up; reason: the base mission's convention for the log-cost RAM
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.22, pp.29–30 (pdf pp.31–32)

import Mathlib
import Definitions.Def_TargetedSamplers_Supplement_SVN
import Definitions.Def_TargetedSamplers_InPrBPTC
import Definitions.Def_TargetedSamplers_InPrDTIME
import Definitions.Def_TargetedSamplers_TimeConstructible

namespace TargetedSamplers.Supplement

/-- Theorem 4.22 (overhead-free quantified derandomization from circuit lower bounds) (Chen, Doron,
Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, pp.29–30). For
any `ϵ > 0` there is a constant `α` such that: if some `L ∈ DTIME[2ⁿ]` has, for every `n`, a truth
table printable in time `2^{(1+α)n}`, but cannot be computed by SVN circuits of size
`2^{(1−α/4)n}`, then for `B(T) = 2^{(1−ϵ)T}`, `prBPTIME_B[T] ⊆ prDTIME[T^{1+O(ϵ)}]`.

**Formalization Note** The `O(ϵ)` is `c · ϵ` with a universal constant `c > 0` chosen before `ϵ`;
`α > 0` depends on `ϵ`. `T` is unquantified on the page; it is read as the `T` of Theorem 4.2, which
the proof applies: time-constructible and increasing (`Monotone`), for every such `T`. The SVN lower
bound holds for all sufficiently large `n` (`SVNHardAE`). `prBPTIME_B[T]` is the base
`InPrBPTIME` (`T` coins, error `B(T)/2^T`). Real powers are rounded up; time is `budget`. -/
theorem theorem_4_22 : ∃ c : ℝ, 0 < c ∧ ∀ ϵ : ℝ, 0 < ϵ → ∃ α : ℝ, 0 < α ∧
    ∀ L : Set (List Bool), InDTIMEExp L →
      TruthTablePrintable L (fun n => ⌈(2 : ℝ) ^ ((1 + α) * n)⌉₊) →
      SVNHardAE L (fun n => (2 : ℝ) ^ ((1 - α / 4) * n)) →
      ∀ T : ℕ → ℕ, TimeConstructible T → Monotone T →
      ∀ PP : KarpLiptonOM.PromiseProblem, InPrBPTIME (fun C => (2 : ℝ) ^ ((1 - ϵ) * C)) T PP →
        InPrDTIME (fun n => ⌈(T n : ℝ) ^ (1 + c * ϵ)⌉₊) PP := by sorry

end TargetedSamplers.Supplement
