-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_entry_7_4_1_a
-- name    : RamanujanLostNotebook.PartV.entry_7_4_1_a
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T18:24:46.351435+00:00
-- url     : https://prove2.me/theorems/3571f1a3-bfc2-4d3a-979b-d9687b9aa188
-- title:
--   (q;q)_∞ φ_6(q) as a sum of two Lambert-type series
-- statement:
--   For $0<|q|<1$: $(q;q)_\infty\,\phi_6(q)=1-2\sum_{n\in\mathbb Z}\dfrac{q^{(2n+1)(3n+1)}}{1+q^{3n+1}}+2\sum_{n\ge1}\dfrac{q^{n(6n+1)}}{1-q^n+q^{2n}}$, where $\phi_6(q)=\sum_{n\ge0}(-1)^n(q;q^2)_nq^{n^2}/(-q;q)_{2n}$; both series converge absolutely. Differs from the printed source: the hypothesis $q\ne0$ is added (the bilateral series contain negative powers of $q$; restriction ours).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 7, Entry 7.4.1, p. 132, eq. (7.4.33).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPhi6
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf

namespace RamanujanLostNotebook.PartV
theorem entry_7_4_1_a (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ∃ S T : ℂ,
      HasSum (fun n : ℤ => q ^ ((2 * n + 1) * (3 * n + 1)) / (1 + q ^ (3 * n + 1))) S ∧
      HasSum (fun m : ℕ => q ^ ((m + 1) * (6 * m + 7)) / (1 - q ^ (m + 1) + q ^ (2 * (m + 1)))) T ∧
      qPochInf q q * mockPhi6 q = 1 - 2 * S + 2 * T := by sorry
end RamanujanLostNotebook.PartV
