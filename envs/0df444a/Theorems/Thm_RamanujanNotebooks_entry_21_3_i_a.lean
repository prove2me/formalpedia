-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_21_3_i_a
-- name    : RamanujanNotebooks.entry_21_3_i_a
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T04:29:01.271635+00:00
-- url     : https://prove2.me/theorems/47fda75d-5a65-4b44-8da2-3dc6ca9262df
-- title:
--   The combination 1 + 12 sum k q^k/(1-q^k) - 36 sum k q^(3k)/(1-q^(3k)) as the square of a Lambert series mod 3 and as a quotient of psi functions
-- statement:
--   Let $q\in\mathbb C$, $|q|<1$; $L(q)=1-24\sum_{k\ge1}kq^k/(1-q^k)$, $\varphi(q)=\sum_{n\in\mathbb Z}q^{n^2}$, $\psi(q)=\sum_{n\ge0}q^{n(n+1)/2}$, $\chi(q)=(-q;q^2)_\infty$, and $(q;q)_\infty$ is Ramanujan's $f(-q)$. With $S=\sum_{n\ge0}\Big(\dfrac{q^{3n+1}}{1-q^{3n+1}}-\dfrac{q^{3n+2}}{1-q^{3n+2}}\Big)$ (absolutely convergent): $$\tfrac12\big(3L(q^3)-L(q)\big)=(1+6S)^2=\Big\{\frac{\psi(q)^4+3q\,\psi(q^3)^4}{\psi(q)\psi(q^3)}\Big\}^2 .$$ The left side is $1+12\sum_{k\ge1}\frac{kq^k}{1-q^k}-36\sum_{k\ge1}\frac{kq^{3k}}{1-q^{3k}}$.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part III (Springer, 1991), Chapter 21, Entry 3(i), first, second and fourth expressions, p. 460.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_eisP
import Definitions.Def_RamanujanNotebooks_shared_thetaPsi

namespace RamanujanNotebooks
theorem entry_21_3_i_a (q : ℂ)
    (hq : ‖q‖ < 1) :
    (∃ S : ℂ, HasSum (fun n : ℕ => q ^ (3 * n + 1) / (1 - q ^ (3 * n + 1)) - q ^ (3 * n + 2) / (1 - q ^ (3 * n + 2))) S ∧
      (3 * eisP (q ^ 3) - eisP q) / 2 = (1 + 6 * S) ^ 2) ∧
      (3 * eisP (q ^ 3) - eisP q) / 2 = ((thetaPsi q ^ 4 + 3 * q * thetaPsi (q ^ 3) ^ 4) / (thetaPsi q * thetaPsi (q ^ 3))) ^ 2 := by sorry
end RamanujanNotebooks
