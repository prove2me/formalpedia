-- Prove2me | Theorems.Thm_Puder_limsup_sum_ncard_crit_rpow_le_rhoStair
-- name    : Puder.limsup_sum_ncard_crit_rpow_le_rhoStair
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T09:41:17.009508+00:00
-- url     : https://prove2.me/theorems/2136c227-f846-480a-a8b9-d7c2a40c9d80
-- title:
--   Puder, Corollary 4.5 — limsup (Σ_{π(w)=m} |Crit(w)|)^{1/t} ≤ ρ_m over words of length t, for k ≥ 2 and 1 ≤ m ≤ k
-- statement:
--   Let $k \ge 2$ and $1 \le m \le k$. For $t \ge 0$ let
--   $$c_t = \sum_{\substack{1 \le i_1, \dots, i_t \le 2k \\ \pi(g_{i_1} \cdots g_{i_t}) = m}} |\mathrm{Crit}(g_{i_1} \cdots g_{i_t})|,$$
--   the sum over all $(2k)^t$ words of length $t$ in $g_1, \dots, g_k$ and $g_{k+i} = g_i^{-1}$ (not necessarily reduced) whose reduction in $\mathbf F_k$ has primitivity rank $m$ (`Puder.primitivityRank`, `Puder.Crit`; the word is `List.ofFn` of the letters, reduced by `StrongConv.wordFree`). Then the sequence $c_t^{1/t}$ is eventually bounded above and
--   $$\limsup_{t \to \infty} c_t^{1/t} \le \rho_m,$$
--   where $\rho_m = 2\sqrt{2k-1}$ if $2m - 1 \le \sqrt{2k-1}$ and $\rho_m = 2m - 1 + \frac{2k-1}{2m-1}$ otherwise (`StrongConv.rhoStair k m`). The boundedness conjunct makes the real-valued limit superior the usual one.
--
--   Puder, p. 18: “**Corollary 4.5.** *For every $k \ge 2$ and $m \in \{1, \dots, k\}$, $$\limsup_{t\to\infty} \Big[\sum_{w \in \mathcal{CW}_t^m(B_{\frac d2})} |\mathrm{Crit}(w)|\Big]^{1/t} \le \begin{cases} 2\sqrt{2k-1} & 2m-1 \le \sqrt{2k-1} \\ \frac{2k-1}{2m-1} + 2m - 1 & 2m-1 \ge \sqrt{2k-1} \end{cases}.$$*” Here $B_{\frac d2}$ is the bouquet with $k$ loops, and $\mathcal{CW}_t^m(B_{\frac d2})$ is the set of words in $(X \cup X^{-1})^t$ with primitivity rank $m$ (pp. 7–9); the two cases agree when $2m - 1 = \sqrt{2k-1}$.
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 18).
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 18, Corollary 4.5

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder

open Filter

namespace Puder

theorem limsup_sum_ncard_crit_rpow_le_rhoStair (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        (∑ i : Fin t → Fin k ⊕ Fin k with
            primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ))) atTop ≤ StrongConv.rhoStair k m := by
  sorry

end Puder
