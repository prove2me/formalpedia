-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_entry_4_1_4
-- name    : RamanujanLostNotebook.PartV.entry_4_1_4
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T16:48:42.021986+00:00
-- url     : https://prove2.me/theorems/0cf25406-8ab9-48b0-a166-50b4bb7fe754
-- title:
--   Identity relating phi_3(iq), phi_3(-iq), f_{sqrt 2}(q) and psi(-q)
-- statement:
--   Let $|q|<1$, $\tilde\phi(q)=\sum_{n\ge0}q^{n^2}/(-q^2;q^2)_n$ (the third order mock theta function $\phi_3$) and $\psi(q)=\sum_{n\ge0}q^{n(n+1)/2}$. Then $\tfrac12(1+e^{\pi i/4})\tilde\phi(iq)+\tfrac12(1+e^{-\pi i/4})\tilde\phi(-iq)=f_{\sqrt2}(q)+\frac{1}{\sqrt2}\psi(-q)(-q^2;q^4)_\infty\prod_{n\ge1}\frac{1}{1+\sqrt2q^n+q^{2n}}$. Here $f_a(q)=\sum_{n\ge0}q^{n^2}/\prod_{j=1}^{n}(1+aq^j+q^{2j})$ (equation (4.1.3)).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 4, Entry 4.1.4, p. 37, eq. (4.1.10).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPhi3
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartV_shared_rankA
import Definitions.Def_RamanujanLostNotebook_PartV_shared_thetaPsi

namespace RamanujanLostNotebook.PartV
theorem entry_4_1_4 (q : ℂ) (hq : ‖q‖ < 1) :
    (1 + Complex.exp ((Real.pi : ℂ) * Complex.I / 4)) / 2 * mockPhi3 (Complex.I * q)
        + (1 + Complex.exp (-((Real.pi : ℂ) * Complex.I / 4))) / 2 * mockPhi3 (-(Complex.I * q)) =
      rankA ((Real.sqrt 2 : ℝ) : ℂ) q
        + 1 / ((Real.sqrt 2 : ℝ) : ℂ) * thetaPsi (-q) * qPochInf (-(q ^ 2)) (q ^ 4)
          * (∏' n : ℕ, 1 / (1 + ((Real.sqrt 2 : ℝ) : ℂ) * q ^ (n + 1) + q ^ (2 * (n + 1)))) := by sorry
end RamanujanLostNotebook.PartV
