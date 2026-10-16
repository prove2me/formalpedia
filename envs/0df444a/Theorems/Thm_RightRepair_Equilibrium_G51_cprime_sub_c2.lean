-- Prove2me | Theorems.Thm_RightRepair_Equilibrium_G51_cprime_sub_c2
-- name    : RightRepair.Equilibrium.G51_cprime_sub_c2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:28.795976+00:00
-- url     : https://prove2.me/theorems/47736b5c-020f-4875-a05f-a0808926eec3
-- title:
--   (G.51), OA p. 42 — separation of two production-cost cutoffs
-- statement:
--   For the cutoffs $\underline c'$ and $c_2$ defined on OA p. 40, the paper's identity is
--
--   $$
--   \underline c'-c_2=(2-f)\bigl(c_M-(2c_I-\delta)\bigr).
--   $$
--
--   If $c_I<(\delta+c_M)/2$, this difference is positive. The identity orders the first two cost regimes used in the low independent-repair-cost part of Table 1.
--
--   **Formalization Note** The standing assumptions include the disclosed $c,c_M\ge0$ pins; $0<f<1$ and $0<\delta<1$ ensure the cutoff formulas' denominators are nonzero.
-- source:
--   Jin, Yang & Zhu, Right to Repair: Pricing, Welfare, and Environmental Implications, authors' manuscript of Management Science (2022), doi:10.1287/mnsc.2022.4401 (PDF sha256 b869b33a…1763), OA p. 42, (G.51) (PDF 75); definitions OA p. 40 (PDF 73)

import Mathlib
import Definitions.Def_RightRepair_Equilibrium_Setting

namespace RightRepair.Equilibrium

theorem G51_cprime_sub_c2 (P : Params) (hP : Standing P) :
    cPrimeLow P - c2 P =
      (2 - P.f) * (P.cM - (2 * P.cI - P.δ)) ∧
    (P.cI < (P.δ + P.cM) / 2 → 0 < cPrimeLow P - c2 P) := by sorry

end RightRepair.Equilibrium
