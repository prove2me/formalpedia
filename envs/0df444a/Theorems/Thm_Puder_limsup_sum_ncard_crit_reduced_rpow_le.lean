-- Prove2me | Theorems.Thm_Puder_limsup_sum_ncard_crit_reduced_rpow_le
-- name    : Puder.limsup_sum_ncard_crit_reduced_rpow_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T10:16:28.828082+00:00
-- url     : https://prove2.me/theorems/37f747f1-489f-4838-840a-6f816eab4e10
-- title:
--   Puder, Proposition 4.3 — limsup (Σ_{|w|=t, π(w)=m} |Crit(w)|)^{1/t} ≤ max(√(2k−1), 2m−1) over reduced words, for k ≥ 2 and 1 ≤ m ≤ k
-- statement:
--   Let $k \ge 2$ and $1 \le m \le k$. For $t \ge 0$ let
--   $$a_t = \sum_{\substack{w \in \mathbf F_k,\ |w| = t \\ \pi(w) = m}} |\mathrm{Crit}(w)|,$$
--   the sum over the elements of $\mathbf F_k$ of reduced length $t$ with respect to $g_1, \dots, g_k$ whose primitivity rank is $m$ (`Puder.primitivityRank`, `Puder.Crit`). In the Lean, the sum runs over the $(2k)^t$ letter sequences of length $t$ in $g_i$ and $g_i^{-1}$ (the word is `List.ofFn` of the letters, reduced by `StrongConv.wordFree`) whose reduction has length $t$ (`FreeGroup.toWord`); these are the reduced words, one for each element of length $t$. Then the sequence $a_t^{1/t}$ is eventually bounded above and
--   $$\limsup_{t \to \infty} a_t^{1/t} \le \begin{cases} \sqrt{2k-1} & 2m - 1 \le \sqrt{2k-1}, \\ 2m - 1 & \text{otherwise.} \end{cases}$$
--   The boundedness conjunct makes the real-valued limit superior the usual one. As in the bundle, $|\mathrm{Crit}(w)|$ is `Set.ncard`, which is $0$ for an infinite set; Puder's Theorem 2.3 says that $\mathrm{Crit}(w)$ is finite (`Puder.crit_finite_and_isBigO_uniformExp_card_fixedPoints`).
--
--   Puder, p. 15: “**Proposition 4.3.** *Let $k \ge 2$ and $m \in \{1, 2, \dots, k\}$. Then $$\limsup_{t\to\infty} \Big[\sum_{\substack{w \in \mathbf F_k: \\ |w| = t\ \&\ \pi(w) = m}} |\mathrm{Crit}(w)|\Big]^{1/t} \le \begin{cases} \sqrt{2k-1} & 2m-1 \le \sqrt{2k-1} \\ 2m-1 & 2m-1 \ge \sqrt{2k-1} \end{cases}.$$*” The two cases agree when $2m - 1 = \sqrt{2k-1}$.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 15), Proposition 4.3.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 15, Proposition 4.3

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

open Filter

namespace Puder

theorem limsup_sum_ncard_crit_reduced_rpow_le (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) atTop ≤
        if (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1) then Real.sqrt (2 * k - 1) else 2 * m - 1 := by
  sorry

end Puder
