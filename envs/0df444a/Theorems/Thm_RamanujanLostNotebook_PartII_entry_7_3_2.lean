-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartII_entry_7_3_2
-- name    : RamanujanLostNotebook.PartII.entry_7_3_2
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T02:54:50.605983+00:00
-- url     : https://prove2.me/theorems/775288c1-c4e3-40de-a3c1-e6fce167e36e
-- title:
--   Sum of tails of the distinct-part product
-- statement:
--   For |q|<1 let S=(-q;q)_∞. All three series converge absolutely, and sum q^(n(n+1)/2)/(-q;q)_n = 2(S/2 + sum(S−(-q;q)_n) − S sum_{n≥1}q^n/(1−q^n)). Define the following summands, with indices in L: nonnegative integers, A: nonnegative integers, B: nonnegative integers: $L(n)=\frac{(q)^{\frac{(n)((n+1))}{2}}}{(-(q);q)_{n}}$; $A(n)=((-(q);q)_{\infty}-(-(q);q)_{n})$; $B(n)=\frac{(q)^{(n+1)}}{(1-(q)^{(n+1)})}$. Then $\sum_{n\ge0} L(n)=(2)(((\frac{(-(q);q)_{\infty}}{2}+\sum_{n\ge0} A(n))-((-(q);q)_{\infty})(\sum_{n\ge0} B(n))))$. Here $(u;q)_n=\prod_{j=0}^{n-1}(1-uq^j)$ and $(u;q)_\infty=\prod_{j\ge0}(1-uq^j)$; $\varphi(u)=\sum_{k\in\mathbb Z}u^{k^2}$ when it occurs. Differs from the printed source: we make the analytic domain |q|<1 explicit; on this domain all displayed denominators are nonzero, and absolute convergence is asserted in the conclusion. This clarification is ours; the formula is unchanged.
--
--   **Discrepancy from the printed source.** Differs from the printed source: we make the analytic domain |q|<1 explicit; on this domain all displayed denominators are nonzero, and absolute convergence is asserted in the conclusion. This clarification is ours; the formula is unchanged.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 7, Entry 7.3.2, p. 163.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf

namespace RamanujanLostNotebook.PartII
theorem entry_7_3_2 (q : ℂ) (hq : ‖q‖ < 1) :
    let L : ℕ → ℂ := fun n => q ^ (n * (n + 1) / 2) / qPoch (-q) q n;
    let A : ℕ → ℂ := fun n => qPochInf (-q) q - qPoch (-q) q n;
    let B : ℕ → ℂ := fun n => q ^ (n + 1) / (1 - q ^ (n + 1));
    Summable L ∧ Summable A ∧ Summable B ∧
    (∑' n : ℕ, L n) = 2 * (qPochInf (-q) q / 2 + (∑' n : ℕ, A n) - qPochInf (-q) q * (∑' n : ℕ, B n)) := by sorry
end RamanujanLostNotebook.PartII
