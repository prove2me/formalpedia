-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_9_4_1
-- name    : RamanujanLostNotebook.PartI.entry_9_4_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:15:41.860196+00:00
-- url     : https://prove2.me/theorems/a0d509ab-cdb9-490e-af14-d76be1a06cf3
-- title:
--   Parameter pentagonal false theta series
-- statement:
--   For complex q with |q|<1 and arbitrary complex a, satisfying 1+a q^(k+1) is nonzero for every k≥0, all series below converge absolutely and the used infinite products converge, and $\sum_{n\ge0}\frac{(({(-1)}^{n}\,{a}^{(2\,n)})\,{q}^{\frac{(n\,(n+1))}{2}})}{(((-a)\,q);q)_{n}}=g(a)$. The notation is $(x;t)_n=\prod_{k=0}^{n-1}(1-x t^k)$ and $(x;t)_\infty=\prod_{k\ge0}(1-x t^k)$. Define $\phi(x)=\sum_{n\ge0}x^n q^{n(n+1)/2}/(bq;q)_n$ and $g(x)=\sum_{n\ge0}x^{3n}q^{n(3n+1)/2}(1-x^2q^{2n+1})$ as needed. Differs from the printed source: we explicitly require |q|<1 and 1+a q^(k+1) is nonzero for every k≥0; the printed Entry does not list these analytic regularity conditions. Absolute convergence is stated in the conclusion, rather than assumed. These domain choices are ours. Independent pre-compile audit confirmation: the current analytic statement has maximum residual 3.622272e-71 and audit accuracy label 70w at q=0.25, q=-0.65, q=0.36+0.48i, and the q=0 and a=0 edges. The audit used 70 decimal digits and 320/640 terms or factors. These are numerical checks, not proofs or certified tail bounds.
--
--   **Discrepancy from the printed source.** Differs from the printed source: we explicitly require |q|<1 and 1+a q^(k+1) is nonzero for every k≥0; the printed Entry does not list these analytic regularity conditions. Absolute convergence is stated in the conclusion, rather than assumed. These domain choices are ours. Independent pre-compile audit confirmation: the current analytic statement has maximum residual 3.622272e-71 and audit accuracy label 70w at q=0.25, q=-0.65, q=0.36+0.48i, and the q=0 and a=0 edges. The audit used 70 decimal digits and 320/640 terms or factors. These are numerical checks, not proofs or certified tail bounds.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 9, Entry 9.4.1, p. 232, eq. (9.4.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch09_ch09G
import Definitions.Def_RamanujanLostNotebook_PartI_ch09_ch09GTerm
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch

namespace RamanujanLostNotebook.PartI
theorem entry_9_4_1 (q : ℂ) (a : ℂ) (hq : ‖q‖ < 1)
    (hden : ∀ k : ℕ, 1 + a * q ^ (k + 1) ≠ 0) :
    Summable (fun n : ℕ => (((((-1 : ℂ) ^ n) * (a ^ (2 * n))) * (q ^ ((n * (n + 1)) / 2))) / (qPoch ((-a) * q) q n))) ∧
    Summable (ch09GTerm q a) ∧
    (∑' n : ℕ, (((((-1 : ℂ) ^ n) * (a ^ (2 * n))) * (q ^ ((n * (n + 1)) / 2))) / (qPoch ((-a) * q) q n))) = (ch09G q a) := by sorry
end RamanujanLostNotebook.PartI
