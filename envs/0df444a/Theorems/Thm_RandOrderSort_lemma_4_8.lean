-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_8
-- name    : RandOrderSort.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:18.478971+00:00
-- url     : https://prove2.me/theorems/55621ac0-6786-4a3c-9ea9-560c4c257d65
-- title:
--   Lemma 4.8 — half-sample overflow
-- statement:
--   Fix a growing phase $j$, its strictly ordered enlarged prefix $P_{j+1}$ of $2t_j$ elements, and a strict cut in this set, allowing either outer cut. Conditional on $P_{j+1}$, the earlier prefix $P_j$ is a uniform $t_j$-subset. The empirical partition tree constructed from $P_j$ has $g_j=t_j/T$ leaves, and $P_{j+1}\setminus P_j$ comprises the arrivals of phase $j$. At a level with $2s$ leaves per parent, each child of the selected parent has $s$ buckets and capacity $2Ts$. Then
--   $$\mathbb P\bigl(\exists\text{ child }I:|(P_{j+1}\setminus P_j)\cap I|>2Ts\bigm|P_{j+1}\bigr)\le A_ge^{-Ts/224},\qquad A_g=2+1027^2.$$
--   The bound is independent of the values in $P_{j+1}$ and of the cut.
--
--   This is the tail bound for the arrival charge of a growing phase under reverse exposure.
--
--   Differences from the source:
--   - encoding: conditional on the strictly ordered set P_{j+1} → a fixed population {0, …, 2t_j−1} in its natural order and a uniform t_j-subset S; reason: only the order of P_{j+1} matters, and this states the bound for every fixed set, as in the page's proof ("Fix P_{j+1}"), which implies the conditional statement
--   - encoding: a strict cut in the set, allowing either outer cut → the position c ∈ {0, …, 2t_j} between population elements; reason: the same cuts
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.8, p.27, display (35)

import Mathlib
import Definitions.Def_RandOrderSort_mkTree
import Definitions.Def_RandOrderSort_phaseStart
import Definitions.Def_RandOrderSort_Gj

namespace RandOrderSort

/-- **Lemma 4.8 (Half-sample overflow)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.27: "Fix a growing phase j, its strictly ordered
enlarged prefix P_{j+1} of 2t_j elements, and a strict cut in this set, allowing either outer cut.
Conditional on P_{j+1}, the earlier prefix P_j is a uniform t_j-subset. The empirical partition tree
constructed from P_j has g_j = t_j/T leaves, and P_{j+1} \ P_j comprises the arrivals of phase j. At
a level with 2s leaves per parent, each child of the selected parent has s buckets and capacity 2Ts.
Then P(∃ child I : |(P_{j+1} \ P_j) ∩ I| > 2Ts | P_{j+1}) ≤ A_g e^{−Ts/224}, A_g = 2 + 1027². (35)
The bound is independent of the values in P_{j+1} and of the cut."

**Formalization Note.** Conditioning on `P_{j+1}` is fixing it: only its
order matters, so it is the population `{0, …, 2t_j − 1}` in its natural order; `P_j` is a uniform
`t_j`-subset `S`; the cut lies between population elements `c − 1` and `c`, `0 ≤ c ≤ 2t_j`. The tree
is (7) on `S` with `2^j` leaves, the scale is `s = 2^h`, the selected parent is the node of height
`h + 1` containing the cut. The statement is posed for every `j ≥ 0`. -/
theorem lemma_4_8 : ∀ j c : ℕ, c ≤ 2 * tj j → ∀ h : ℕ, 2 ^ (h + 1) ≤ 2 ^ j →
    subsetProb (2 * tj j) (tj j) (fun S => ∃ e < 2,
        2 * T * 2 ^ h < countIn natLt (mkTree natLt S (2 ^ j)) (Finset.range (2 * tj j) \ S) h
          (2 * (cutLeaf (fun a => decide (c ≤ a)) (mkTree natLt S (2 ^ j)) / 2 ^ (h + 1)) + e)) ≤
      Ag * Real.exp (-((T : ℝ) * 2 ^ h / 224)) := by sorry

end RandOrderSort
