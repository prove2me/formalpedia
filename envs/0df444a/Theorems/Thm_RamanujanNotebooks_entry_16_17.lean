-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_16_17
-- name    : RamanujanNotebooks.entry_16_17
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T03:15:22.539986+00:00
-- url     : https://prove2.me/theorems/488b1814-129c-4c49-8f75-71e112db82d2
-- title:
--   Ramanujan's 1ψ1 summation
-- statement:
--   Let $|q|<1$, $\alpha,\beta\ne0$, $|\beta q|<|z|$ and $|z|\,|\alpha q|<1$, $\alpha q^{2k},\beta q^{2k}\ne1$ ($k\ge1$). Then $1+\sum_{k\ge1}\dfrac{(1/\alpha;q^2)_k(-\alpha q)^k}{(\beta q^2;q^2)_k}z^k+\sum_{k\ge1}\dfrac{(1/\beta;q^2)_k(-\beta q)^k}{(\alpha q^2;q^2)_k}z^{-k}=\dfrac{(-qz;q^2)_\infty(-q/z;q^2)_\infty}{(-\alpha qz;q^2)_\infty(-\beta q/z;q^2)_\infty}\cdot\dfrac{(q^2;q^2)_\infty(\alpha\beta q^2;q^2)_\infty}{(\alpha q^2;q^2)_\infty(\beta q^2;q^2)_\infty}$. Differs from the printed source: the nonvanishing hypotheses are made explicit. The upper annulus condition is written without division. This includes $q=0$, where all positive-index series terms vanish and the identity reduces to $1=1$.
--
--   **Discrepancy from the printed source.** Book, p. 32: '|beta q| < |z| < 1/|alpha q|'. Added by us: alpha, beta != 0, alpha q^(2k) != 1, beta q^(2k) != 1 (k >= 1). The upper annulus condition is written without division. This includes q=0, where all positive-index series terms vanish and the identity reduces to 1=1. (Audit: at q=0, alpha=2, beta=3, z=4 all hypotheses hold and both sides are 1.)
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part III (Springer, 1991), Chapter 16, Entry 17, p. 32, eq. (17.1).

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_qPoch
import Definitions.Def_RamanujanNotebooks_shared_qPochInf

namespace RamanujanNotebooks
theorem entry_16_17 (α β z q : ℂ) (hq : ‖q‖ < 1) (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    (h1 : ‖β * q‖ < ‖z‖) (h2 : ‖z‖ * ‖α * q‖ < 1)
    (hα : ∀ k : ℕ, α * q ^ (2 * k + 2) ≠ 1) (hβ : ∀ k : ℕ, β * q ^ (2 * k + 2) ≠ 1) :
    ∃ s t : ℂ,
      HasSum (fun k : ℕ => qPoch (1 / α) (q ^ 2) (k + 1) * (-(α * q)) ^ (k + 1)
          / qPoch (β * q ^ 2) (q ^ 2) (k + 1) * z ^ (k + 1)) s ∧
      HasSum (fun k : ℕ => qPoch (1 / β) (q ^ 2) (k + 1) * (-(β * q)) ^ (k + 1)
          / qPoch (α * q ^ 2) (q ^ 2) (k + 1) * (1 / z) ^ (k + 1)) t ∧
      1 + s + t =
        qPochInf (-(q * z)) (q ^ 2) * qPochInf (-(q / z)) (q ^ 2)
            / (qPochInf (-(α * q * z)) (q ^ 2) * qPochInf (-(β * q / z)) (q ^ 2))
          * (qPochInf (q ^ 2) (q ^ 2) * qPochInf (α * β * q ^ 2) (q ^ 2)
            / (qPochInf (α * q ^ 2) (q ^ 2) * qPochInf (β * q ^ 2) (q ^ 2))) := by sorry
end RamanujanNotebooks
