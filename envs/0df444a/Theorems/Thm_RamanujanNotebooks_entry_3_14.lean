-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_3_14
-- name    : RamanujanNotebooks.entry_3_14
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T22:28:54.156988+00:00
-- url     : https://prove2.me/theorems/1fe95886-3ef1-4819-a725-3a91cc3f37c4
-- title:
--   Lambert's series for a root of a q x^p - x^q + 1 = 0
-- statement:
--   Let $p,q>0$, $p\ne q$, $c_0(n)=1$, $c_1(n)=n$, $c_k(n)=n\prod_{j=1}^{k-1}(n+kp-jq)$, and let $a$ be real with $|a|\le p^{-p/q}|p-q|^{(p-q)/q}$. Then there is a real $x>0$ with $aqx^p-x^q+1=0$ such that for every real $n$, $$\sum_{k\ge0}\frac{c_k(n)a^k}{k!}=x^n.$$
--
--   **Discrepancy from the printed source.** The definition on p. 70 allows complex $a$, and Entry 14 on p. 71 refers to a root without fixing its branch. This version takes $a$ real and asserts existence of a positive real root. Real powers of that root then have an unambiguous meaning for every real $n$. The polynomial coefficient formula and parameter bound (14.3) are retained.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 3, Entry 14, p. 71, eq. (14.4).

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch03_ch3C

namespace RamanujanNotebooks
theorem entry_3_14 (p q a : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (ha : |a| ≤ p ^ (-(p / q)) * |p - q| ^ ((p - q) / q)) :
    ∃ x : ℝ, 0 < x ∧ a * q * x ^ p - x ^ q + 1 = 0 ∧
      ∀ n : ℝ, HasSum (fun k : ℕ => ch3C p q k n * a ^ k / (k.factorial : ℝ)) (x ^ n) := by sorry
end RamanujanNotebooks
