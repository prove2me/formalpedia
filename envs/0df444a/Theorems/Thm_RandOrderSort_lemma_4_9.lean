-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_9
-- name    : RandOrderSort.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:38.414897+00:00
-- url     : https://prove2.me/theorems/9896450a-65d8-46aa-9e12-41f630cdf6b2
-- title:
--   Lemma 4.9 — reallocation after a half-split
-- statement:
--   Let $n\ge 8192$, and condition on the enlarged prefix set $P_{j+1}$. Consider the two children $I$ of the selected $2s$-leaf parent in the new tree, and put $Z(I)=|P_j\cap I|$. If $j<J$, the new tree is a growing tree, each child has $s$ buckets of capacity $2T$, and
--   $$\mathbb P\bigl(\exists I:2Z(I)+4T>2Ts\bigm|P_{j+1}\bigr)\le 2e^{-Ts/96}\qquad(s\ge 8).$$
--   If $j=J$, the new tree is the first shrinking tree with $b=b_1$ finest leaves, each child has capacity at least $Bs$, and
--   $$\mathbb P\bigl(\exists I:2Z(I)+4T>Bs\bigm|P_L\bigr)\le 2e^{-Bs/100}\qquad(s\ge 64).$$
--   Each event contains the corresponding local reallocation-overflow event: on every execution, a node of the new tree whose old-cell requests locally overflow satisfies the corresponding inequality.
--
--   Together with Lemma 4.8 this gives the witness tails used in the reverse conditional product of Lemma 4.10.
--
--   Differences from the source:
--   - encoding: conditional on the set P_{j+1} → a fixed population {0, …, 2t_j−1} in its natural order and a uniform t_j-subset S, with the new tree (7) on the whole population; reason: as in Lemma 4.8
--   - generalization: the overflow inclusion for the two children of the selected parent → the inclusion for every node of the new tree with s = 2^h ≤ its leaf count; reason: the children of the selected parent are such nodes, so it specializes to the page's sentence
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.9, p.29, displays (38), (39)

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort
import Definitions.Def_RandOrderSort_Dop
import Definitions.Def_RandOrderSort_Gj

namespace RandOrderSort

/-- **Lemma 4.9 (Reallocation after a half-split)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.29: "Conditional on the enlarged prefix
set P_{j+1}, consider the two children I of the selected 2s-leaf parent in the new tree. If j < J, the
new tree is a growing tree, and each child has s buckets of capacity 2T. Then
P(∃ I : 2Z(I) + 4T > 2Ts | P_{j+1}) ≤ 2e^{−Ts/96} (s ≥ 8). (38) If j = J, the new tree is the first
shrinking tree, with b = b_1 finest leaves, and each child has capacity at least Bs. Then
P(∃ I : 2Z(I) + 4T > Bs | P_L) ≤ 2e^{−Bs/100} (s ≥ 64), (39) where P_j = P_J and P_{j+1} = P_L. Each
event above contains the corresponding local reallocation-overflow event."

**Formalization Note.** For `n ≥ 8192` and a growing phase `j ≤ J`. As in Lemma 4.8 the fixed
`P_{j+1}` is the population `{0, …, 2t_j − 1}` (for `j = J`, `2t_J = m`), `P_j` a uniform
`t_j`-subset `S` and `Z(I) = |S ∩ I|`; the new tree is (7) on the whole population (`2^{j+1}` leaves,
resp. `b_1`). The last sentence is stated on every execution of the run, for every node `I` of the
new tree with `s = 2^h ≤` its leaf count (children of the selected parent included): if the old-cell
requests of the following reallocation locally overflow `I`, then `2Z(I) + 4T` exceeds `2Ts`
(`j < J`), resp. `Bs` (`j = J`), with `Z(I)` the number of the first `t_j` keys canonical in `I`. -/
theorem lemma_4_9 : ∀ n, 16 * T ≤ n → ∀ j ≤ J n,
    (j < J n → ∀ c ≤ 2 * tj j, ∀ h : ℕ, 8 ≤ 2 ^ h → 2 ^ (h + 1) ≤ 2 ^ (j + 1) →
      subsetProb (2 * tj j) (tj j) (fun S => ∃ e < 2,
          2 * T * 2 ^ h < 2 * countIn natLt (mkTree natLt (Finset.range (2 * tj j)) (2 ^ (j + 1))) S h
            (2 * (cutLeaf (fun a => decide (c ≤ a))
              (mkTree natLt (Finset.range (2 * tj j)) (2 ^ (j + 1))) / 2 ^ (h + 1)) + e) + 4 * T) ≤
        2 * Real.exp (-((T : ℝ) * 2 ^ h / 96))) ∧
    (j = J n → ∀ c ≤ m n, ∀ h : ℕ, 64 ≤ 2 ^ h → 2 ^ (h + 1) ≤ b n 1 →
      subsetProb (m n) (tj (J n)) (fun S => ∃ e < 2,
          B n * 2 ^ h < 2 * countIn natLt (mkTree natLt (Finset.range (m n)) (b n 1)) S h
            (2 * (cutLeaf (fun a => decide (c ≤ a))
              (mkTree natLt (Finset.range (m n)) (b n 1)) / 2 ^ (h + 1)) + e) + 4 * T) ≤
        2 * Real.exp (-((B n : ℝ) * 2 ^ h / 100))) ∧
    ∀ (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)) (h idx : ℕ), 2 ^ h ≤ phaseLeaves n (j + 1) →
      Overflows (opReqs (runOf x π σ) (j + 1) false) (phaseLeaves n (j + 1)) (phaseCap n (j + 1)) h idx →
        (if j < J n then 2 * T * 2 ^ h else B n * 2 ^ h) <
          2 * countIn (ltOf x π σ) (phaseTree n (ltOf x π σ) (j + 1)) (Finset.range (tj j)) h idx +
            4 * T := by sorry

end RandOrderSort
