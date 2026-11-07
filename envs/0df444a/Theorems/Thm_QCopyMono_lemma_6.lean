-- Prove2me | Theorems.Thm_QCopyMono_lemma_6
-- name    : QCopyMono.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:46.535206+00:00
-- url     : https://prove2.me/theorems/5ebca37a-c9a5-4de0-a780-aa4248b2b94b
-- title:
--   Lemma 6 (Path soundness) — some scale $d$ has $p_{t_d}(f)\ge c_1\varepsilon t_d d^{3/8}/n$
-- statement:
--   There are absolute constants $c_0,c_1,n_0>0$, with moreover $c_0\le1$, such that the following holds. Let $n\ge n_0$ and $0<\varepsilon\le1/2$. For each $d\in\mathcal D_n=\{1,2,4,\dots,2^{\lfloor\log_2 n\rfloor}\}$ let
--   $$
--   t_d=\max\{1,\lfloor c_0\varepsilon\sqrt n\,d^{-5/8}\rfloor\}.
--   $$
--   If $f:\{0,1\}^n\to\{0,1\}$ is $\varepsilon$-far from monotone and $I[f]\le2\sqrt n$, then for some $d\in\mathcal D_n$,
--   $$
--   p_{t_d}(f)\ge\frac{c_1\,\varepsilon\,t_d\,d^{3/8}}{n}.
--   $$
--   This is the classical soundness of the path experiment that the quantum path tester estimates.
--
--   Differences from the source:
--   - generalization: absolute constants c_0, c_1, n_0 > 0 → the same with moreover c_0 ≤ 1; reason: stronger; the proof chooses c_0 ≤ min{1/40, c/(20000C)} ≤ 1, and Lemma 7 ("t_d as in Lemma 6") needs t_d built from a c_0 ≤ 1
--   - encoding: d ∈ D_n = {1, 2, 4, …, 2^{⌊log_2 n⌋}}; n_0 > 0 → d = 2^j with 2^j ≤ n; n_0 a positive natural number; reason: the same set of d; n ≥ n_0 for a real n_0 is n ≥ ⌈n_0⌉
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), Lemma 6, p.13 (proof in Appendix A.1, pp.35–39)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_Influence
import Definitions.Def_QCopyMono_PathExperiment

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), Lemma 6 (Path soundness), p.13 (proof in
Appendix A.1, pp.35–39): there are absolute constants `c₀, c₁, n₀ > 0` such that for `n ≥ n₀`,
`0 < ε ≤ 1/2`, `t_d = max{1, ⌊c₀ ε √n d^{−5/8}⌋}` for `d ∈ Dₙ = {1, 2, 4, …, 2^{⌊log₂ n⌋}}`, and
`f` `ε`-far from monotone with `I[f] ≤ 2√n`, some `d ∈ Dₙ` has
`p_{t_d}(f) ≥ c₁ ε t_d d^{3/8}/n`.

**Formalization Note.** `d = 2^j` with `2^j ≤ n`. The constant `c₀` is also asserted to satisfy
`c₀ ≤ 1` (the proof chooses `c₀ ≤ min{1/40, c/(20000C)}`), so that the lengths `t_d` of this
lemma are lengths to which Lemma 7 applies ("with `t_d` as in Lemma 6"). -/
theorem lemma_6 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ 0 < c₁ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ f : Qubits n → Bool,
        IsFar ε f → influence f ≤ 2 * Real.sqrt n →
          ∃ j : ℕ, 2 ^ j ≤ n ∧
            c₁ * ε * (pathLen c₀ ε n ((2 : ℝ) ^ j) : ℝ) * ((2 : ℝ) ^ j) ^ (3 / 8 : ℝ) / n ≤
              pathProb ε (pathLen c₀ ε n ((2 : ℝ) ^ j)) f := by sorry

end QCopyMono
