-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_entry_13_3_1_a
-- name    : RamanujanLostNotebook.PartIV.entry_13_3_1_a
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T15:52:44.471228+00:00
-- url     : https://prove2.me/theorems/aaca605a-64d6-4e46-9024-76e899dcde7b
-- title:
--   Ramanujan-Guinand transformation for the digamma function
-- statement:
--   Let $\varphi(x)=\psi(x)+\frac1{2x}-\log x$ and $\alpha,\beta>0$ with $\alpha\beta=1$. The series $\sum_{n\ge1}\varphi(n\alpha)$, $\sum_{n\ge1}\varphi(n\beta)$ converge absolutely and $\sqrt\alpha\Bigl\{\frac{\gamma-\log(2\pi\alpha)}{2\alpha}+\sum_{n\ge1}\varphi(n\alpha)\Bigr\}=\sqrt\beta\Bigl\{\frac{\gamma-\log(2\pi\beta)}{2\beta}+\sum_{n\ge1}\varphi(n\beta)\Bigr\}$.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 13, Entry 13.3.1, p. 293, eq. (13.3.3).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIV_ch13_digammaRemainder
import Definitions.Def_RamanujanLostNotebook_PartIV_shared_riemannXi
import Definitions.Def_RamanujanLostNotebook_PartIV_shared_riemannXiUpper
open MeasureTheory

namespace RamanujanLostNotebook.PartIV
theorem entry_13_3_1_a (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α * β = 1) :
    Summable (fun n : ℕ => digammaRemainder (((n : ℝ) + 1) * α)) ∧
    Summable (fun n : ℕ => digammaRemainder (((n : ℝ) + 1) * β)) ∧
    Real.sqrt α * ((Real.eulerMascheroniConstant - Real.log (2 * Real.pi * α)) / (2 * α)
        + ∑' n : ℕ, digammaRemainder (((n : ℝ) + 1) * α))
      = Real.sqrt β * ((Real.eulerMascheroniConstant - Real.log (2 * Real.pi * β)) / (2 * β)
        + ∑' n : ℕ, digammaRemainder (((n : ℝ) + 1) * β)) := by sorry
end RamanujanLostNotebook.PartIV
