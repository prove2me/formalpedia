-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_theorem_2
-- name    : ProportionalGroupDivision.Main.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:54.456976+00:00
-- url     : https://prove2.me/theorems/cacd2f1d-bb0d-4d48-846f-ec46717e9790
-- title:
--   Theorem 2 — $\Omega(\sqrt{n/k})\le\mathrm{PROP}(n_1,\dots,n_k)\le O(\sqrt{(n/k)(\ln^3(n_1k/n)+1)})$, with a randomized polynomial-time allocation
-- statement:
--   Fix an integer $k\ge2$ and positive integers $n_1\ge\dots\ge n_k$, and put $n=\sum_{i=1}^k n_i$ and
--
--   $$F(k,\mathbf n)=\sqrt{\frac nk\cdot\Big(\ln^3\Big(\frac{n_1k}{n}\Big)+1\Big)} .$$
--
--   There are absolute constants $a,b>0$, not depending on $k$ or the sizes, such that
--
--   $$a\sqrt{\frac nk}\ \le\ \mathrm{PROP}(n_1,\dots,n_k)\ \le\ b\,F(k,\mathbf n).$$
--
--   Additionally, the allocation in the upper bound can be computed in randomized polynomial time: there is one randomized algorithm which, for every such $k$ and sizes, every finite set of $m$ goods and every table of nonnegative additive valuations $\mu_{(i,j)}$, runs within a polynomial number $c_0(n+m+k+1)^e$ of steps and, with probability at least $2/3$, outputs a partition $G=B_1\sqcup\dots\sqcup B_k$ satisfying PROP-$c$ for some positive integer $c\le b\,F(k,\mathbf n)$.
--
--   This determines $\mathrm{PROP}$ up to a polylogarithmic factor in $n_1k/n$ for arbitrary group sizes; for equal sizes the two bounds match up to constants.
--
--   **Formalization Note** The algorithm is one program of the real-arithmetic fragment `InFragment` of the published `PolySampIso` real RAM (exact arithmetic, comparisons, $\sqrt{\cdot}$, standard Gaussian draws, unit cost per instruction), chosen together with $a,b,c_0,e$ before every input; it reads the input layout `fdInput` and writes the group of good $g$ into memory cell $-1-g$. It halts within the bound on every random tape, and the success event contains a measurable set of tapes of probability at least $2/3$. $\mathrm{PROP}$ is compared through `ℝ≥0∞`, so the upper bound includes its finiteness.
--
--   Differences from the source:
--   - encoding: Ω(·) and O(·) → explicit constants a, b > 0 chosen before k and the group sizes; reason: the meaning of the asymptotic notation, uniform in all parameters
--   - encoding: an arbitrary finite set G of goods → Fin m for every m ∈ ℕ, including m = 0; reason: every finite set is in bijection with some Fin m
--   - encoding: PROP the smallest positive integer c → PROP in ℕ∞ (∞ if no integer works), compared in ℝ≥0∞; reason: the upper bound asserts finiteness; the same value when finite
--   - reading: the allocation in our upper bound can be computed in randomized polynomial time (footnote 1: randomness for the random walk of [LM12]) → one program of the PolySampIso real-RAM fragment (exact arithmetic, comparisons, √, standard Gaussian draws, unit cost), chosen before all inputs, halting within c₀(n + m + k + 1)^e steps on every random tape, whose output is a PROP-c partition with c ≤ bF on a measurable set of tapes of probability ≥ 2/3; reason: the paper fixes neither a machine nor a success probability; inputs are real valuations and the randomness is Gaussian (footnote 1); success probability 2/3 in worst-case polynomial time is the standard meaning of a randomized polynomial-time algorithm, and any constant above 0 is equivalent by independent restarts with a polynomial check of the output
--   - encoding: input and output of the algorithm → sizes in pointer registers, valuations in memory (agents lexicographically, goods in order), group of good g in memory cell −1 − g; reason: a fixed layout of the same data
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Theorem 2 and footnote 1, PDF p. 2 = printed p. 2; via Lemma 3 (p. 4), Theorem 4 (p. 4) and the algorithmic consequence of Appendix A (PDF p. 24)

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Model
import Definitions.Def_ProportionalGroupDivision_Main_Machine

open scoped BigOperators ENNReal

namespace ProportionalGroupDivision.Main

/-- Theorem 2 (PDF p. 2, with footnote 1): there are absolute constants `a, b > 0` and one
randomized real-arithmetic program `P` (fragment `InFragment`) with a polynomial step bound
`c₀ (n + m + k + 1)^e`, all chosen before the instance, such that for every `k ≥ 2` and all positive
integers `n_1 ≥ ⋯ ≥ n_k`, with `n = n_1 + ⋯ + n_k` and `F = √((n/k)(ln³(n_1 · k/n) + 1))`:
1. `a √(n/k) ≤ PROP(n_1, …, n_k) ≤ b F`;
2. for every finite set of `m` goods and every nonnegative additive valuation table `μ`, the run of
   `P` on `fdInput n μ` halts within `c₀ (n + m + k + 1)^e` steps on every random tape, and with
   probability at least `2/3` (a measurable set of tapes) its output (memory cells `−1, …, −m`) is a
   partition `σ : Fin m → Fin k` satisfying PROP-`c` for some positive integer `c ≤ b F`. -/
theorem theorem_2 :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∃ P : PolySampIso.Program, InFragment P ∧ ∃ c₀ e : ℕ,
      ∀ (k : ℕ) (hk : 2 ≤ k) (n : Fin k → ℕ), Antitone n → (∀ i, 0 < n i) →
        ENNReal.ofReal (a * Real.sqrt ((∑ i, (n i : ℝ)) / k)) ≤ ((PROP n : ℕ∞) : ℝ≥0∞) ∧
        ((PROP n : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (b * Real.sqrt ((∑ i, (n i : ℝ)) / k *
          (Real.log ((n ⟨0, by omega⟩ : ℝ) * k / ∑ i, (n i : ℝ)) ^ 3 + 1))) ∧
        ∀ (m : ℕ) (μ : Valuation n m), IsNonneg μ →
          (∀ ω, HaltsWithin P (fdInput n μ) ω
            ((c₀ : ℝ) * ((∑ i, (n i : ℝ)) + m + k + 1) ^ e)) ∧
          ∃ E : Set PolySampIso.Streams, MeasurableSet E ∧ (2 / 3 : ℝ≥0∞) ≤ PolySampIso.tape E ∧
            ∀ ω ∈ E, ∃ σ : Fin m → Fin k,
              (∀ g : Fin m, outCell (finalState P (fdInput n μ) ω) g = ((σ g : ℕ) : ℝ)) ∧
              ∃ c : ℕ, 0 < c ∧
                (c : ℝ) ≤ b * Real.sqrt ((∑ i, (n i : ℝ)) / k *
                  (Real.log ((n ⟨0, by omega⟩ : ℝ) * k / ∑ i, (n i : ℝ)) ^ 3 + 1)) ∧
                IsPROP c μ σ := by sorry

end ProportionalGroupDivision.Main
