-- Prove2me | Theorems.Thm_SellingData_AppendsBinary_willingness_to_pay
-- name    : SellingData.AppendsBinary.willingness_to_pay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:43.640924+00:00
-- url     : https://prove2.me/theorems/d14d4e7c-5761-4160-816d-c04ac584b95c
-- title:
--   §3.2, p. 13 — willingness to pay for a data append: U_ij − U_i0 = −T_j + σ_l(α_j)[c_i − v_l(α_j)], increasing in c_i
-- statement:
--   Consider the data-append model with costs $c_L<c_H<\hat u$, a menu with plans $(T_H,\alpha_H)$, $(T_L,\alpha_L)$, and a plan $j\in\{H,L\}$ with $\alpha_j\in[\underline\alpha,\bar\alpha]$. Then for each type $i\in\{H,L\}$ the willingness to pay for plan $j$ over the outside option $U_{i0}=\max\{\hat u-c_i,0\}$ is
--   $$U_{ij}-U_{i0}=-T_j+\sigma_l(\alpha_j)\,[c_i-v_l(\alpha_j)] .$$
--   Moreover, the map $c\mapsto -T_j+\sigma_l(\alpha_j)[c-v_l(\alpha_j)]$ is strictly increasing, and in particular the high-cost type values plan $j$ strictly more than the low-cost type:
--   $$U_{Lj}-U_{L0}<U_{Hj}-U_{H0}.$$
--
--   This is why, with data appends and costs below the prior mean, the high-cost marketers become the "high type" of the screening problem, reversing the roles they have with marketing lists.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 13, §3.2, second paragraph

import Mathlib
import Definitions.Def_SellingData_AppendsBinary_Setting

namespace SellingData.AppendsBinary

open Model

/-- §3.2, p. 13: when `c_L < c_H < û`, a marketer's willingness to pay for plan `(T_j, α_j)`,
`U_ij − U_i0`, equals `−T_j + σ_l(α_j)[c_i − v_l(α_j)]`, which is increasing in `c_i`. -/
theorem willingness_to_pay (M : Model) (hcH : M.cH < M.uHat) (m : Menu) (j : SellingData.ListsBinary.CostType)
    (hαj : m.α j ∈ Set.Icc M.aLo M.aHi) :
    (∀ i : SellingData.ListsBinary.CostType,
        M.U m i j - M.outside (M.c i) = -(m.T j) + M.σl (m.α j) * (M.c i - M.vl (m.α j))) ∧
      StrictMono (fun c : ℝ => -(m.T j) + M.σl (m.α j) * (c - M.vl (m.α j))) ∧
      M.U m SellingData.ListsBinary.CostType.L j - M.outside M.cL < M.U m SellingData.ListsBinary.CostType.H j - M.outside M.cH := by sorry

end SellingData.AppendsBinary
