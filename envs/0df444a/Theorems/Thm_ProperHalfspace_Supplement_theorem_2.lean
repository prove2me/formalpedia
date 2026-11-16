-- Prove2me | Theorems.Thm_ProperHalfspace_Supplement_theorem_2
-- name    : ProperHalfspace.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:50:51.910208+00:00
-- url     : https://prove2.me/theorems/ef09f382-6c1e-4908-b0ba-3e83de3c8903
-- title:
--   Theorem 2 — a sample-based proper agnostic learner for halfspaces (corrected: $n\ge1$)
-- statement:
--   There is one finite program on the sample-access real RAM and a universal constant $C$ such that the following holds for every $n\ge1$, every $\varepsilon\in(0,1/2)$ and every distribution $D$ on $\{\pm1\}^n\times\{\pm1\}$ whose marginal on $\{\pm1\}^n$ is uniform, the program reading $D$ only through independent labeled examples. Write
--   $$S=n^{C\varepsilon^{-2}\log(1/\varepsilon)}\,(1/\varepsilon)^{C},\qquad W=S+2^{C\varepsilon^{-14}\log(1/\varepsilon)}.$$
--
--   1. On every coin tape and every sample stream the program halts after reading at most $S$ labeled examples and after at most $W$ units of work.
--   2. With probability at least $2/3$, over its fair coins and independent examples from $D$, the halfspace $g(x)=\operatorname{sign}(w\cdot x-\theta)$ it outputs satisfies
--   $$\mathrm{err}_D(g)\le\mathrm{OPT}_D+\varepsilon.$$
--
--   The learner matches the additive guarantee and the dependence on $n$ of $L_1$ polynomial regression while returning a halfspace (p.2).
--
--   **Formalization Note** The input is $n$ in pointer $0$ and $\varepsilon$ in memory cell $0$; the output is $w_i$ in cell $i$, for $i<n$, and $\theta$ in cell $n$, so the output is always a halfspace. Powers are real powers and $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - correction: every n, with n^{O(ε⁻² log(1/ε))} poly(1/ε) examples → n ≥ 1; reason: false at n = 0: the example bound is 0^{positive}·poly(1/ε) = 0, and the distributions with D(·,1) = 1 and D(·,−1) = 1 both satisfy every assumption with OPT_D = 0, so error ≤ ε < 1/2 forces the right constant, which no example-free program outputs with probability ≥ 2/3 for both
--   - reading: the real-RAM model, with no instruction set named (p.2) → the sample-access machine ProperHalfspace.Supplement.SampleMachine (the published machine's instructions, without query, with sample at cost n + 1); reason: the page names no instructions; every primitive added would weaken the theorem
--   - reading: "for every ε ∈ (0, 1/2), there is an algorithm" → one program P, chosen before n, ε and D, that reads ε from its input; reason: the stronger of the two readings, and the one the proof gives (one algorithm with accuracy parameter ε); the literal order ("Let D be any distribution … there is an algorithm") would let the algorithm depend on D and output its best halfspace with no examples
--   - reading: "uses … labeled examples and runs in time at most" → both bounds hold on every coin tape and every sample stream; reason: the proof fixes the number of rounds "on every execution" (p.33) and fixed batch sizes
--   - encoding: O(·) and poly(1/ε) → one constant C chosen before all the data, poly(1/ε) = (1/ε)^C; reason: the page's constants are universal (p.10)
--   - encoding: probability over the algorithm's coins and the independent examples → a finite sum over coin tapes and example streams of length the work bound, rounded up, weighted by 2^{−B} ∏ D(σ_k); reason: a run within B units of work reads at most B coins and at most B examples
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Theorem 2, p.2 (restated p.30, proof pp.33–34)

import Mathlib
import Definitions.Def_ProperHalfspace_Halfspace
import Definitions.Def_ProperHalfspace_Machine
import Definitions.Def_ProperHalfspace_Supplement_LabeledDist
import Definitions.Def_ProperHalfspace_Supplement_SampleMachine

namespace ProperHalfspace

namespace Supplement

/-- Theorem 2, p.2, restated p.30 (sample-based proper agnostic learner). De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344
(Nov. 1, 2026). One finite program on the sample-access real RAM, with one universal `C`: for every `n ≥ 1`,
`ε ∈ (0, 1/2)` and every distribution `D` on `{±1}ⁿ × {±1}` with uniform marginal on `{±1}ⁿ`, on every coin tape and every
sample stream the program halts after at most `n^{C ε⁻² log(1/ε)} (1/ε)^C` samples and
`n^{C ε⁻² log(1/ε)} (1/ε)^C + 2^{C ε⁻¹⁴ log(1/ε)}` units of work, and with probability at least `2/3` (over fair coins and
independent examples from `D`) its output `(w, θ)` satisfies `err_D(sign(w · x − θ)) ≤ OPT_D + ε`.

**Formalization Note.** The input is `n` in pointer `0` and `ε` in `M[0]`; the output is `M[i] = wᵢ` for `i < n` and
`M[n] = θ`, so every halted state decodes to a halfspace (proper). The program reads `D` only through `sample` (no
membership query). `O(·)` and `poly(1/ε)` are one constant `C` chosen before `n`, `ε`, `D`; powers are real powers and `log`
is the natural logarithm. The probability is over tapes and streams of length the work bound (rounded up), which no run
reads past. The bounds hold on every tape and stream. `n ≥ 1` corrects the page: at `n = 0` the sample bound is `0`. -/
theorem theorem_2 : ∃ P : SProgram, SAdmissible P ∧ ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ D : Example n → ℝ, IsUniformMarginal D →
      let S : ℝ := (n : ℝ) ^ ((C : ℝ) * (1 / ε) ^ 2 * Real.log (1 / ε)) * (1 / ε) ^ C
      let W : ℝ := S + (2 : ℝ) ^ ((C : ℝ) * (1 / ε) ^ 14 * Real.log (1 / ε))
      (∀ tape : ℕ → Bool, ∀ stream : ℕ → Example n, ∃ t : ℕ,
        let s := srun P stream tape (sInit n ε) t
        s.st.halted = true ∧ (s.samples : ℝ) ≤ S ∧ (s.st.work : ℝ) ≤ W) ∧
      2 / 3 ≤ sampleProb D ⌈W⌉₊ (fun tape stream => ∃ t : ℕ,
        let s := srun P stream tape (sInit n ε) t
        s.st.halted = true ∧
          errD D (ltf (decodeNormal n s.st) (decodeThreshold n s.st)) ≤ optD D + ε) := by sorry

end Supplement

end ProperHalfspace
