-- Prove2me | Theorems.Thm_Puder_limsup_card_wordFree_eq_one_rpow
-- name    : Puder.limsup_card_wordFree_eq_one_rpow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T09:41:17.599604+00:00
-- url     : https://prove2.me/theorems/47cde36f-0df4-4a84-8fa1-efd5838e6728
-- title:
--   Puder, Claim 4.7 — limsup over t of |{w ∈ (X ∪ X⁻¹)^t : w reduces to 1}|^{1/t} is 2√(2k−1)
-- statement:
--   Let $k \ge 2$. For $t \ge 0$ let $e_t$ be the number of words $g_{i_1} \cdots g_{i_t}$ of length $t$ in $g_1, \dots, g_k$ and $g_{k+i} = g_i^{-1}$ ($1 \le i_1, \dots, i_t \le 2k$) that reduce to the identity of $\mathbf F_k$ (the word is `List.ofFn` of the letters, reduced by `StrongConv.wordFree`). Then the sequence $e_t^{1/t}$ is eventually bounded above and
--   $$\limsup_{t \to \infty} e_t^{1/t} = 2\sqrt{2k-1}.$$
--   The boundedness conjunct makes the real-valued limit superior the usual one. For odd $t$, $e_t = 0$ and $0^{1/t} = 0$.
--
--   Puder, p. 18: “Finally, for $m = 0$ there is exactly one relevant reduced word: $w = 1$, and this word has exactly one critical subgroup: the trivial subgroup. Thus, it suffices to bound the number of words in $(X \cup X^{-1})^t$ reducing to 1. This is a well-known result: **Claim 4.7.** $$\limsup_{t\to\infty} \big|\mathcal{CW}_t^0(B_{\frac d2})\big|^{1/t} = \limsup_{t\to\infty} \Big|\Big\{w \in (X \cup X^{-1})^t \;\Big|\; w \text{ reduces to } 1\Big\}\Big|^{1/t} = 2\sqrt{2k-1}.$$” Puder's section works with $k \ge 2$ (Corollary 4.5, “For every $k \ge 2$”).
--
--   Source: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, p. 18).
-- source:
--   Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), p. 18, Claim 4.7

import Mathlib
import Definitions.Def_StrongConv

open Filter

namespace Puder

theorem limsup_card_wordFree_eq_one_rpow (k : ℕ) (hk : 2 ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            StrongConv.wordFree (List.ofFn fun j => some (i j)) = 1).card : ℝ) ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            StrongConv.wordFree (List.ofFn fun j => some (i j)) = 1).card : ℝ) ^ (1 / (t : ℝ)))
        atTop = 2 * Real.sqrt (2 * k - 1) := by
  sorry

end Puder
