-- Prove2me | Theorems.Thm_PharmaEPR_Welfare_proposition_2
-- name    : PharmaEPR.Welfare.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:24.836011+00:00
-- url     : https://prove2.me/theorems/d8bc92aa-fb6d-4163-90bd-195ffd6ae1b4
-- title:
--   Proposition 2, p. 16 — collection-cost threshold for over-prescription under EC
-- statement:
--   In the stated regime, let $u_p\ge\bar u_p^{EC}$ and let collection cost be below $\bar k(u_p)=3(1-2\beta-u_p)/2$. For every EC collection rate $r\in[0,1]$, an over-prescribing feasible producer action earns strictly more than every feasible action that avoids over-prescription:
--
--   $$k<\bar k(u_p)\quad\Longrightarrow\quad
--   \Pi_m^{EC}(\text{some over-prescribing action};r)>
--   \Pi_m^{EC}(\text{every no-over-prescribing action};r).$$
--
--   The collection obligation cannot deter the producer from inducing over-prescription in this low-cost region.
-- source:
--   Alev, Atasu, Toktay & Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020-09-05 posting), p. 16, Proposition 2; proof Online Appendix p. 2

import Mathlib
import Definitions.Def_PharmaEPR_Welfare_Model

namespace PharmaEPR.Welfare

theorem proposition_2 (P : Params) (hP : Regime P) :
    uEC P ≤ P.up → P.k < kBar P →
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 →
        ∃ a, ProdFeasible P a ∧ OverPrescribes P a ∧
          ∀ a', ProdFeasible P a' → ¬ OverPrescribes P a' →
            prodProfit P .EC ⟨r, 0⟩ a' < prodProfit P .EC ⟨r, 0⟩ a := by sorry

end PharmaEPR.Welfare
