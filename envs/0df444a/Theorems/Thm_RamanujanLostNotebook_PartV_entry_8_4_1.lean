-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_entry_8_4_1
-- name    : RamanujanLostNotebook.PartV.entry_8_4_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T17:38:17.706299+00:00
-- url     : https://prove2.me/theorems/863b1fcc-e6b1-45ab-a67e-688de7b95447
-- title:
--   First tenth order identity: phi_10(q^3) and psi_10 at omega q^{1/3}
-- statement:
--   Let $\phi_{10}(q)=\sum_{n\ge0}q^{n(n+1)/2}/(q;q^2)_{n+1}$, $\psi_{10}(q)=\sum_{n\ge1}q^{n(n+1)/2}/(q;q^2)_{n}$, let $\omega$ be a primitive cube root of unity, $|r|<1$ and $q=r^3$ (so $r$ is a cube root $q^{1/3}$). Then $r^{2}\phi_{10}(q^3)-\dfrac{\psi_{10}(\omega r)-\psi_{10}(\omega^2 r)}{\omega-\omega^2}=-\,r\,\dfrac{\sum_{n\in\mathbb{Z}}(-1)^n r^{n^2}\,\sum_{m\in\mathbb{Z}}(-1)^m q^{m(5m+3)/2}}{(q;q^2)_\infty\sum_{n\in\mathbb{Z}}(-1)^n q^{n^2}}$.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 8, Entry 8.4.1, p. 170, eq. (8.4.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPhi10
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPsi10
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf

namespace RamanujanLostNotebook.PartV
theorem entry_8_4_1 (q r ω : ℂ) (hr : ‖r‖ < 1) (hq : q = r ^ 3) (hω : ω ^ 2 + ω + 1 = 0) :
    r ^ 2 * mockPhi10 (q ^ 3)
        - 1 / (ω - ω ^ 2) * (mockPsi10 (ω * r) - mockPsi10 (ω ^ 2 * r))
      = -(r * (∑' n : ℤ, (-1 : ℂ) ^ n * r ^ (n.natAbs ^ 2)) *
            (∑' m : ℤ, (-1 : ℂ) ^ m * q ^ (m * (5 * m + 3) / 2).toNat))
          / (qPochInf q (q ^ 2) * ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n.natAbs ^ 2)) := by sorry
end RamanujanLostNotebook.PartV
