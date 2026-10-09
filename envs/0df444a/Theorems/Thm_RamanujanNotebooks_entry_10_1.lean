-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_10_1
-- name    : RamanujanNotebooks.entry_10_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T01:13:26.493004+00:00
-- url     : https://prove2.me/theorems/03cffed6-a10d-48a7-8535-80993150bf80
-- title:
--   Dougall's theorem for a terminating very well poised 7F6 (one of x, y, z, u a positive integer)
-- statement:
--   Let $N\ge1$ be an integer, $x=N$, and let $n,y,z,u$ be complex. Then the terminating series (terms $k=0,\dots,N$) satisfies $${}_7F_6\Bigl[{n,\ \frac n2+1,\ -x,\ -y,\ -z,\ -u,\ x+y+z+u+2n+1\atop \frac n2,\ x+n+1,\ y+n+1,\ z+n+1,\ u+n+1,\ -x-y-z-u-n};1\Bigr]=\frac{\Gamma(x+n+1)\Gamma(y+n+1)\Gamma(z+n+1)\Gamma(u+n+1)\Gamma(x+y+z+n+1)}{\Gamma(n+1)\Gamma(x+y+n+1)\Gamma(y+z+n+1)\Gamma(x+u+n+1)\Gamma(z+u+n+1)}\cdot\frac{\Gamma(y+z+u+n+1)\Gamma(x+u+z+n+1)\Gamma(x+y+u+n+1)}{\Gamma(x+z+n+1)\Gamma(y+u+n+1)\Gamma(x+y+z+u+n+1)}.$$ (The book's hypothesis is that at least one of $x,y,z,u$, $-x-y-z-u-2n-1$ is a positive integer; by symmetry the first four cases are this one, the fifth is `entry_10_1_b`.) Assumed: none of $n/2$, $-x-y-z-u-n$ and the sixteen Gamma arguments is $0$ or a negative integer. Differs from the printed source: the book gives no condition on the parameters beyond the one quoted; the hypothesis that the listed lower parameters and Gamma (digamma) arguments are not 0 or a negative integer is added by us (it excludes vanishing denominators and poles, where Lean's values are not the classical ones).
--
--   **Discrepancy from the printed source.** Book, p. 9: hypothesis only 'at least one of x, y, z, u, -x-y-z-u-2n-1 is a positive integer'. Our statement: the book gives no condition on the parameters beyond the one quoted; the hypothesis that the listed lower parameters and Gamma (digamma) arguments are not 0 or a negative integer is added by us (it excludes vanishing denominators and poles, where Lean's values are not the classical ones).
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part II (Springer, 1989), Chapter 10, Entry 1, p. 9, eq. (1.1).

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_hypPFQTerm

namespace RamanujanNotebooks
theorem entry_10_1 (N : ℕ) (hN : 1 ≤ N) (n x y z u : ℂ) (h1 : x = (N : ℂ))
    (h2 : ∀ w ∈ ([n / 2, -x - y - z - u - n, x + n + 1, y + n + 1, z + n + 1, u + n + 1,
        x + y + z + n + 1, y + z + u + n + 1, x + u + z + n + 1, x + y + u + n + 1, n + 1,
        x + y + n + 1, y + z + n + 1, x + u + n + 1, z + u + n + 1, x + z + n + 1, y + u + n + 1,
        x + y + z + u + n + 1] : List ℂ), ∀ j : ℕ, w ≠ -(j : ℂ)) :
    ∑ k ∈ Finset.range (N + 1), hypPFQTerm [n, n / 2 + 1, -x, -y, -z, -u,
        x + y + z + u + 2 * n + 1] [n / 2, x + n + 1, y + n + 1, z + n + 1, u + n + 1,
        -x - y - z - u - n] 1 k
      = Complex.Gamma (x + n + 1) * Complex.Gamma (y + n + 1) * Complex.Gamma (z + n + 1) *
          Complex.Gamma (u + n + 1) * Complex.Gamma (x + y + z + n + 1) / (Complex.Gamma (n + 1) *
          Complex.Gamma (x + y + n + 1) * Complex.Gamma (y + z + n + 1) *
          Complex.Gamma (x + u + n + 1) * Complex.Gamma (z + u + n + 1)) *
          (Complex.Gamma (y + z + u + n + 1) * Complex.Gamma (x + u + z + n + 1) *
          Complex.Gamma (x + y + u + n + 1) / (Complex.Gamma (x + z + n + 1) *
          Complex.Gamma (y + u + n + 1) * Complex.Gamma (x + y + z + u + n + 1))) := by sorry
end RamanujanNotebooks
