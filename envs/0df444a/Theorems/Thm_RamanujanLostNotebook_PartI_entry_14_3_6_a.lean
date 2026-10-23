-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_14_3_6_a
-- name    : RamanujanLostNotebook.PartI.entry_14_3_6_a
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T02:48:54.174235+00:00
-- url     : https://prove2.me/theorems/3eb6a1f4-f79d-4523-9b68-02065c56152e
-- title:
--   Endpoint-normalized character eta integral
-- statement:
--   For 0<q<1, A(q)=exp(−C−(1/9)∫_q^1 f(−t)⁹/f(−t³)³ dt/t), where A(q)=q^(1/9)∏_{n≥1}(1−q^n)^(nχ₃(n)) and C=(3√3/(4π))∑_{n≥1}χ₃(n)/n². The product and improper integral converge.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 14, Entry 14.3.6, p. 318, eq. (14.3.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch14_ch14A
import Definitions.Def_RamanujanLostNotebook_PartI_ch14_ch14C
import Definitions.Def_RamanujanLostNotebook_PartI_ch14_ch14Chi3
import Definitions.Def_RamanujanLostNotebook_PartI_shared_eulerF
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf
open scoped BigOperators

namespace RamanujanLostNotebook.PartI
theorem entry_14_3_6_a (q : ℝ) (h0 : 0 < q) (h1 : q < 1) :
    Multipliable (fun n : ℕ => (1 - q ^ (n + 1)) ^ (((n + 1 : ℕ) : ℤ) * ch14Chi3 (n + 1))) ∧
    (∀ t : ℝ, t ∈ Set.Ioo q 1 → (eulerF ((t : ℂ) ^ 3)).re ≠ 0) ∧
    MeasureTheory.IntegrableOn (fun t : ℝ => (eulerF (t : ℂ)).re ^ 9 / ((eulerF ((t : ℂ) ^ 3)).re ^ 3 * t)) (Set.Ioo q 1) ∧
    ch14A q = Real.exp (-ch14C - (1 / 9 : ℝ) *
      ∫ t in Set.Ioo q 1, (eulerF (t : ℂ)).re ^ 9 / ((eulerF ((t : ℂ) ^ 3)).re ^ 3 * t)) := by sorry
end RamanujanLostNotebook.PartI
