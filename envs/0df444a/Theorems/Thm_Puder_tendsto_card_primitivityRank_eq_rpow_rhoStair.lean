-- Prove2me | Theorems.Thm_Puder_tendsto_card_primitivityRank_eq_rpow_rhoStair
-- name    : Puder.tendsto_card_primitivityRank_eq_rpow_rhoStair
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T09:41:25.274655+00:00
-- url     : https://prove2.me/theorems/bc75a139-6634-4182-a8d4-b60697ccc1ff
-- title:
--   Puder, Theorem 8.5 (clause m ∈ {1, …, k}) — the number b_{k,m}(t) of words of length t with π(w) = m satisfies b_{k,m}(t)^{1/t} → ρ_m
-- statement:
--   Let $k \ge 2$ and $1 \le m \le k$. For $t \ge 0$ let $b_{k,m}(t)$ be the number of words $g_{i_1} \cdots g_{i_t}$ of length $t$ in $g_1, \dots, g_k$ and $g_{k+i} = g_i^{-1}$ (not necessarily reduced; $1 \le i_1, \dots, i_t \le 2k$) whose reduction in $\mathbf F_k$ has primitivity rank $m$ (`Puder.primitivityRank`; the word is `List.ofFn` of the letters, reduced by `StrongConv.wordFree`). Then
--   $$\lim_{t \to \infty} b_{k,m}(t)^{1/t} = \rho_m,$$
--   where $\rho_m = 2\sqrt{2k-1}$ if $2m - 1 \le \sqrt{2k-1}$ and $\rho_m = 2m - 1 + \frac{2k-1}{2m-1}$ otherwise (`StrongConv.rhoStair k m`).
--
--   Puder, p. 38: “**Theorem 8.5.** *Let $k \ge 2$ and $m \in \{0, 1, 2, \dots, k, \infty\}$. Let $$b_{k,m}(t) = \Big|\Big\{w \in (X \cup X^{-1})^t \;\Big|\; \pi(w) = m\Big\}\Big|.$$ … For $m \in \{1, \dots, k\}$, $$\lim_{t\to\infty} b_{k,m}(t)^{1/t} = \begin{cases} 2\sqrt{2k-1} & 2m-1 \le \sqrt{2k-1} \\ 2m - 1 + \frac{2k-1}{2m-1} & 2m-1 \ge \sqrt{2k-1} \end{cases}.$$*” This statement is that clause only; the theorem's clauses for $m = 0$ (a limit over even $t$) and $m = \infty$ are not included. The two cases agree when $2m - 1 = \sqrt{2k-1}$.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 38).
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 38, Theorem 8.5, the clause m ∈ {1, …, k}

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

open Filter Topology

namespace Puder

theorem tendsto_card_primitivityRank_eq_rpow_rhoStair (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m)
    (hm : m ≤ k) :
    Tendsto (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m).card : ℝ) ^
          (1 / (t : ℝ))) atTop (𝓝 (StrongConv.rhoStair k m)) := by
  sorry

end Puder
