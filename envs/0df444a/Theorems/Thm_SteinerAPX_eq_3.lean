-- Prove2me | Theorems.Thm_SteinerAPX_eq_3
-- name    : SteinerAPX.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:37.343626+00:00
-- url     : https://prove2.me/theorems/5d96d87e-42e3-4350-88e1-eb13a51a4d80
-- title:
--   Eq. (3) — deterministic Johnson–Lindenstrauss: $n$ points into $O(\eta^{-2}\log n)$ dimensions with distortion $1+\eta$, in polynomial time
-- statement:
--   There is a constant $c>0$ such that for every rational $0<\eta<1$ there is a polynomial-time algorithm that maps any $n\ge2$ distinct rational points $p_1,\dots,p_n\in\mathbb R^D$ to rational points $q_1,\dots,q_n\in\mathbb R^k$ (in the same order) with
--   $$
--   k\le c\,\eta^{-2}\log n
--   \qquad\text{and}\qquad
--   \|p_i-p_j\|\le\|q_i-q_j\|\le(1+\eta)\|p_i-p_j\|\quad\text{for all } i,j .
--   $$
--   Display (3) of the paper is the case $\eta=\beta/2$, giving $k=O(\beta^{-2}\log n)=O(\log n)$.
--
--   This reduces the dimension of the instance of Lemma 16 from $O(n)$ to $O(\log n)$ while distorting distances between terminals by at most $1+\eta$.
--
--   **Formalization Note** Inputs and outputs are raw rational terminal sets; the machine is a Mathlib `TM2ComputableInPolyTime` machine with a finite alphabet; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - generalization: distortion 1 + β/2 with k = O(β⁻² log n) → every rational distortion parameter 0 < η < 1 with k ≤ c·η⁻²·log n, c independent of η; reason: the Johnson–Lindenstrauss statement quoted on the same page is for every 0 < η < 1; a rational η ≤ β/2 gives display (3)
--   - encoding: points q₁, …, qₙ ∈ ℝᵏ obtained in polynomial time → rational points, encoded in binary, output by a polynomial-time TM2 machine, for distinct rational input points with n ≥ 2; reason: machine inputs and outputs are finite codes; distinct points and n ≥ 2 are the instances where it is applied, and log n > 0 there
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §5.2, eq. (3), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_SteinerAPX_RawTerminals

namespace SteinerAPX

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Eq. (3): deterministic Johnson–Lindenstrauss embedding in polynomial time.** S. Bartlmae,
*Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…),
§5.2, p.22 (PDF p.24): "The Johnson–Lindenstrauss lemma [29] states that, for every 0 < η < 1, any
n points in a Euclidean space can be mapped into O(η−2 log n) dimensions so that, after rescaling,
every pairwise distance changes by a factor between 1 and 1 + η. Using the deterministic
construction of Engebretsen, Indyk, and O'Donnell [21], we obtain in polynomial time points
q1, …, qn ∈ Rk, k = O(β−2 log n) = O(log n), with ∥pi − pj∥ ≤ ∥qi − qj∥ ≤ (1 + β/2)∥pi − pj∥ for
all i, j. (3)"

There is a constant `c > 0` such that for every rational `0 < η < 1` some polynomial-time machine
maps every valid set of `n ≥ 2` distinct rational points `p₁, …, pₙ ∈ ℝᴰ` to a valid set of `n`
rational points `q₁, …, qₙ ∈ ℝᵏ` (same order) with `k ≤ c η⁻² log n` and
`‖pᵢ − pⱼ‖ ≤ ‖qᵢ − qⱼ‖ ≤ (1 + η)‖pᵢ − pⱼ‖` for all `i, j`.

**Formalization Note** The distortion is a rational parameter `η`; (3) is the case `η = β/2` (or
any rational `η ≤ β/2`). Inputs and outputs are raw terminal sets with rational coordinates
(`rawTerminalsBits`); the machine is a Mathlib `TM2ComputableInPolyTime` with a finite alphabet.
`log` is the natural logarithm; `c` does not depend on `η` or the input. -/
theorem eq_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℚ, 0 < η → η < 1 →
    ∃ f : RawTerminals → RawTerminals,
    ∃ comp : Turing.TM2ComputableInPolyTime rawTerminalsBits rawTerminalsBits f,
      MachineFiniteAlphabet.FiniteAlphabet comp.tm ∧
      ∀ t : RawTerminals, t.Valid → 2 ≤ t.n →
        (f t).Valid ∧ ∃ hn : (f t).2.length = t.2.length,
          ((f t).k : ℝ) ≤ c * ((η : ℝ)⁻¹) ^ 2 * Real.log (t.n : ℝ) ∧
          ∀ i j : Fin t.2.length,
            dist (t.point i) (t.point j) ≤
              dist ((f t).point (Fin.cast hn.symm i)) ((f t).point (Fin.cast hn.symm j)) ∧
            dist ((f t).point (Fin.cast hn.symm i)) ((f t).point (Fin.cast hn.symm j)) ≤
              (1 + (η : ℝ)) * dist (t.point i) (t.point j) := by sorry

end SteinerAPX
