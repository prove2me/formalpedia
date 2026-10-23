-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_letter_f3_bounded_a
-- name    : RamanujanLostNotebook.PartV.letter_f3_bounded_a
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T18:11:57.60922+00:00
-- url     : https://prove2.me/theorems/90efd028-b9c6-40bc-9675-6de1e5659c57
-- title:
--   f_3(q) + (q;q^2)_∞ φ(-q) is bounded radially at the points q^k = -1, k odd
-- statement:
--   Let $f_3(q)=\sum_{n\ge0}q^{n^2}/(-q;q)_n^2$ and $\varphi(-q)=\sum_{n\in\mathbb Z}(-1)^nq^{n^2}$. If $k$ is odd and $\zeta^k=-1$, then $f_3(r\zeta)+(r\zeta;r^2\zeta^2)_\infty\,\varphi(-r\zeta)$ is bounded as $r\to1^-$ ($r$ real).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 14, Section 14.2, last letter, f_3 at the points q^(odd) = -1, p. 313, unnumbered display.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockF3
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartV_shared_thetaPhi

namespace RamanujanLostNotebook.PartV
theorem letter_f3_bounded_a (k : ℕ) (hk : Odd k) (ζ : ℂ) (hζ : ζ ^ k = -1) :
    Asymptotics.IsBigO (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (fun r : ℝ =>
        mockF3 ((r : ℂ) * ζ) + qPochInf ((r : ℂ) * ζ) (((r : ℂ) * ζ) ^ 2) * thetaPhi (-((r : ℂ) * ζ)))
      (fun _ : ℝ => (1 : ℝ)) := by sorry
end RamanujanLostNotebook.PartV
