-- Prove2me | Theorems.Thm_RightRepair_Equilibrium_G39_problem4_opt
-- name    : RightRepair.Equilibrium.G39_problem4_opt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:35.262132+00:00
-- url     : https://prove2.me/theorems/67aea4e9-1c2e-438d-a913-e84c577b8c17
-- title:
--   (G.39), OA p. 22 — full-repair Problem 4 optimum
-- statement:
--   Under the paper's standing assumptions, let $\pi_4(p_n,p_r)$ be the full-repair objective of Problem 4, with its feasible set defined in (G.35). Its optimal value is
--
--   $$
--   \max_{(p_n,p_r)\text{ feasible}}\pi_4(p_n,p_r)
--   =\frac{(c-\delta+c_M f-1)^2}{4(1+3\delta)}.
--   $$
--
--   A feasible maximizer exists, and every feasible point on the line $p_n+fp_r=(c+\delta+c_Mf+1)/2$ attains this value. The line allows several price pairs with the same profit.
--
--   **Formalization Note** The standing assumptions include the nonnegative unit-cost pins. The constraints are the authors' reduced constraints of (G.35), independently of the general equilibrium predicate.
-- source:
--   Jin, Yang & Zhu, Right to Repair: Pricing, Welfare, and Environmental Implications, authors' manuscript of Management Science (2022), doi:10.1287/mnsc.2022.4401 (PDF sha256 b869b33a…1763), OA pp. 20, 22, (G.35), (G.39) (PDF 53, 55)

import Mathlib
import Definitions.Def_RightRepair_Equilibrium_Setting

namespace RightRepair.Equilibrium

theorem G39_problem4_opt (P : Params) (hP : Standing P) :
    let optValue := (P.c - P.δ + P.cM * P.f - 1) ^ 2 / (4 * (1 + 3 * P.δ))
    let optLine := (P.c + P.δ + P.cM * P.f + 1) / 2
    (∀ pn pr : ℝ, feasible4 P pn pr → profit4 P pn pr ≤ optValue) ∧
    (∃ pn pr : ℝ, feasible4 P pn pr ∧ pn + P.f * pr = optLine ∧
      profit4 P pn pr = optValue) ∧
    (∀ pn pr : ℝ, feasible4 P pn pr → pn + P.f * pr = optLine →
      profit4 P pn pr = optValue) := by sorry

end RightRepair.Equilibrium
