-- Prove2me | Theorems.Thm_Puder_tendsto_card_primitivityRank_eq_rpow_of_sqrt_lt
-- name    : Puder.tendsto_card_primitivityRank_eq_rpow_of_sqrt_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T10:32:45.523692+00:00
-- url     : https://prove2.me/theorems/67f07109-e979-447a-a9c8-4a9b3621c8ab
-- title:
--   Puder, Theorem 8.5 (case 2m − 1 > √(2k−1)) — b_{k,m}(t)^{1/t} → 2m − 1 + (2k−1)/(2m−1)
-- statement:
--   Let $k \ge 2$ and $m \le k$ with $2m - 1 > \sqrt{2k-1}$, so that $m \ge 2$. For $t \ge 0$ let $b_{k,m}(t)$ be the number of words $g_{i_1} \cdots g_{i_t}$ of length $t$ in $g_1, \dots, g_k$ and $g_{k+i} = g_i^{-1}$ (not necessarily reduced; $1 \le i_1, \dots, i_t \le 2k$) whose reduction in $\mathbf F_k$ has primitivity rank $m$ (`Puder.primitivityRank`; the word is `List.ofFn` of the letters, reduced by `StrongConv.wordFree`). Then
--   $$\lim_{t \to \infty} b_{k,m}(t)^{1/t} = 2m - 1 + \frac{2k-1}{2m-1}.$$
--
--   Puder, p. 38: “**Theorem 8.5.** *Let $k \ge 2$ and $m \in \{0, 1, 2, \dots, k, \infty\}$. Let $$b_{k,m}(t) = \Big|\Big\{w \in (X \cup X^{-1})^t \;\Big|\; \pi(w) = m\Big\}\Big|.$$ … For $m \in \{1, \dots, k\}$, $$\lim_{t\to\infty} b_{k,m}(t)^{1/t} = \begin{cases} 2\sqrt{2k-1} & 2m-1 \le \sqrt{2k-1} \\ 2m - 1 + \frac{2k-1}{2m-1} & 2m-1 \ge \sqrt{2k-1} \end{cases}.$$*” This statement is the second case with strict inequality; at $2m - 1 = \sqrt{2k-1}$ the two cases agree. Puder's proof treats this case on its own: “If $2m - 1 > \sqrt{2k-1}$, the statement follows from the statements on reduced words (Theorems 8.2 and 8.1) and an application of the extended cogrowth formula [Pud15] (here a bit more elaborated results from [Pud15], not mentioned in Theorem 4.4, are required).”
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 38), Theorem 8.5.
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 38, Theorem 8.5, the case 2m − 1 > √(2k − 1)

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

open Filter Topology

namespace Puder

theorem tendsto_card_primitivityRank_eq_rpow_of_sqrt_lt (k m : ℕ) (hk : 2 ≤ k) (hm : m ≤ k)
    (hlt : Real.sqrt (2 * k - 1) < 2 * m - 1) :
    Tendsto (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m).card : ℝ) ^
          (1 / (t : ℝ))) atTop (𝓝 (2 * m - 1 + (2 * k - 1) / (2 * m - 1))) := by
  sorry

end Puder
