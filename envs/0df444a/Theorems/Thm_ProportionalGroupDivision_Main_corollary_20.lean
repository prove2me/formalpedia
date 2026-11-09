-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_corollary_20
-- name    : ProportionalGroupDivision.Main.corollary_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:27.752186+00:00
-- url     : https://prove2.me/theorems/9794a7cc-59b9-4043-93dc-4a57abb9d517
-- title:
--   Corollary 20 (from Lovett–Meka) — algorithmic partial coloring with probability $\ge 0.1$ in time $\mathrm{poly}(n,m,\delta^{-1})$
-- statement:
--   There is an efficient randomized algorithm with the following guarantee. Its input is a matrix $A\in[0,1]^{n\times m}$, thresholds $c_1,\dots,c_n\ge0$ with
--
--   $$\sum_{j=1}^n \exp(-c_j^2/16)\ \le\ \frac m{16},$$
--
--   an approximation parameter $\delta>0$ and a point $x\in[0,1]^m$. With probability at least $0.1$ it finds a point $x'\in[0,1]^m$ such that, simultaneously,
--
--   1. $|\langle x-x',A_i\rangle|\le c_i\|A_i\|_2$ for every row $i$;
--   2. $x'_i\ge1-\delta$ or $x'_i\le\delta$ for at least $m/2$ indices $i\in[m]$.
--
--   Moreover the algorithm runs in time $\mathrm{poly}(n,m,\delta^{-1})$.
--
--   This is the randomized rounding step behind the efficiency of the whole upper bound.
--
--   **Formalization Note** The algorithm is one program of the real-arithmetic fragment `InFragment` (exact arithmetic, comparisons, $\sqrt{\cdot}$, standard Gaussian draws), chosen before all inputs and run on the input layout `lmInput`. It halts within $c_0(n+m+\delta^{-1}+1)^e$ steps on every random tape, for constants $c_0,e$ fixed with the program, and (1), (2) and $x'\in[0,1]^m$ hold together on a measurable set of tapes of probability at least $1/10$.
--
--   Differences from the source:
--   - generalization: a small approximation parameter δ > 0 → every δ > 0; reason: a guarantee for every positive δ specializes to every small δ
--   - reading: an efficient randomized algorithm with running time poly(n, m, δ⁻¹) → one program of the PolySampIso real-RAM fragment (exact arithmetic, comparisons, √, standard Gaussian draws, unit cost), chosen before all inputs, halting within c₀(n + m + 1/δ + 1)^e steps on every random tape; reason: the paper fixes no machine; real inputs and the Gaussian random walk of [LM12] are the arithmetic model in which this running time is stated
--   - encoding: with probability at least 0.1 finds x′ → the output x′ satisfies x′ ∈ [0,1]^m, (i) and (ii) on a measurable set of tapes of probability ≥ 1/10; reason: an event of probability ≥ 0.1 contains a measurable subset of that probability, and conversely
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Corollary 20 (from Lovett–Meka [LM12], Theorem 5), PDF p. 20 = printed p. 20; Theorem 5, PDF p. 5

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Machine

open scoped BigOperators ENNReal

namespace ProportionalGroupDivision.Main

/-- Corollary 20 (from Lovett–Meka [LM12], PDF p. 20): there is an efficient randomized algorithm
which, given `A ∈ [0,1]^{N×m}`, thresholds `c_1, …, c_N ≥ 0` with `∑_j exp(−c_j²/16) ≤ m/16`, an
approximation parameter `δ > 0` and a point `x ∈ [0,1]^m`, with probability at least `0.1` finds
`x′ ∈ [0,1]^m` such that
(i) `|⟨x − x′, A_i⟩| ≤ c_i ‖A_i‖₂` for every row `i`, and
(ii) `x′_g ≥ 1 − δ` or `x′_g ≤ δ` for at least `m/2` indices `g`;
moreover the algorithm runs in time `poly(N, m, δ⁻¹)`.

The algorithm is one program `P` of the randomized real RAM fragment `InFragment`, chosen before
all inputs, with input `lmInput A c x δ`; it halts within `c₀ (N + m + δ⁻¹ + 1)^e` steps on every
random tape, and its output `x′` (memory cells `−1, …, −m` at the halt) satisfies (i) and (ii)
on a measurable set of tapes of probability at least `1/10`. -/
theorem corollary_20 :
    ∃ P : PolySampIso.Program, InFragment P ∧ ∃ c₀ e : ℕ,
      ∀ (N m : ℕ) (A : Matrix (Fin N) (Fin m) ℝ), (∀ i g, A i g ∈ Set.Icc (0 : ℝ) 1) →
      ∀ c : Fin N → ℝ, (∀ i, 0 ≤ c i) → ∑ i, Real.exp (-(c i) ^ 2 / 16) ≤ (m : ℝ) / 16 →
      ∀ δ : ℝ, 0 < δ → ∀ x : Fin m → ℝ, (∀ g, x g ∈ Set.Icc (0 : ℝ) 1) →
        (∀ ω, HaltsWithin P (lmInput A c x δ) ω ((c₀ : ℝ) * ((N : ℝ) + m + 1 / δ + 1) ^ e)) ∧
        ∃ E : Set PolySampIso.Streams, MeasurableSet E ∧ (1 / 10 : ℝ≥0∞) ≤ PolySampIso.tape E ∧
          ∀ ω ∈ E,
            (∀ g : Fin m, outCell (finalState P (lmInput A c x δ) ω) g ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ i : Fin N, |∑ g, (x g - outCell (finalState P (lmInput A c x δ) ω) g) * A i g| ≤
              c i * Real.sqrt (∑ g, A i g ^ 2)) ∧
            (m : ℝ) / 2 ≤ ((Finset.univ.filter (fun g : Fin m =>
              1 - δ ≤ outCell (finalState P (lmInput A c x δ) ω) g ∨
                outCell (finalState P (lmInput A c x δ) ω) g ≤ δ)).card : ℝ) := by sorry

end ProportionalGroupDivision.Main
