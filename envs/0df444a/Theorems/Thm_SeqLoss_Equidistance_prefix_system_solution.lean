-- Prove2me | Theorems.Thm_SeqLoss_Equidistance_prefix_system_solution
-- name    : SeqLoss.Equidistance.prefix_system_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:13.310158+00:00
-- url     : https://prove2.me/theorems/e60e75da-6755-40b7-8c37-b3a64198d2b4
-- title:
--   Proof of Theorem 2, p. 24 — the prefix system forces $\alpha=L/(2n)$ and, for equal losses, $x=\varphi^{1/2}(\ell)$
-- statement:
--   Let $n\ge 1$, let $\ell\in\mathbb R^n$ have total $L$, and let $x\in\mathbb R^n$ satisfy $x_1+\dots+x_n=L$. Suppose that for some $\alpha\in\mathbb R$
--   $$\sum_{i=1}^k x_i-\frac L2=\alpha k\qquad\text{for }k=1,\dots,n.$$
--   Then
--   1. $\alpha=\dfrac{L}{2n}$;
--   2. if moreover $\ell_1=\dots=\ell_n$, then $x=\varphi^{1/2}(\ell)$, that is $x_1=\frac{L}{2n}+\frac L2$ and $x_2=\dots=x_n=\frac L{2n}$.
--
--   Together with the previous milestone this shows that, for equal losses, an allocation equidistant from the ideal allocations can only be the midpoint rule's.
--
--   **Formalization Note** The paper determines $\alpha$ "through $x_1+\dots+x_n=1$"; the intended equation is $x_1+\dots+x_n=L$, which is the hypothesis here. Agents are 0-based.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 24, Appendix A, proof of Theorem 2, from "Rearranging" to the end of the proof

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_Equidistance_IdealAllocations

namespace SeqLoss.Equidistance
theorem prefix_system_solution {n : ℕ} (hn : 0 < n) (ℓ x : Fin n → ℝ) (α : ℝ)
    (hsum : ∑ i, x i = SeqLoss.FixedFraction.total ℓ)
    (hsys : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x i) - SeqLoss.FixedFraction.total ℓ / 2 = α * (k : ℝ)) :
    α = SeqLoss.FixedFraction.total ℓ / (2 * (n : ℝ)) ∧
      ((∀ i j, ℓ i = ℓ j) → x = SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ) := by sorry
end SeqLoss.Equidistance
