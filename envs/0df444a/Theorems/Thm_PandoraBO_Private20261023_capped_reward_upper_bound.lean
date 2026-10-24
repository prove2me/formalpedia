-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_capped_reward_upper_bound
-- name    : PandoraBO.Private20261023.capped_reward_upper_bound
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:05:33.132631+00:00
-- url     : https://prove2.me/theorems/1de7b00e-6578-4409-9a7a-ecdb45f090fe
-- title:
--   Capped rewards bound every policy’s penalized value
-- statement:
--   For reservation indices at a strictly positive multiplier, cap every box reward at its index. Every policy’s expected reward minus the scaled expected inspection cost is at most the expected maximum of these capped rewards. The finite independent-box model supplies all integrability and independence hypotheses.
-- source:
--   Capped-reward proof of Weitzman’s rule used in Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5, Lemma 7 Part I, equation (42), citing Kleinberg et al., Theorem 1. The inequality and equality cases are separated for the formalization.

import Definitions.Def_PandoraBO_Model
open MeasureTheory PandoraBO
set_option autoImplicit false

theorem PandoraBO.Private20261023.capped_reward_upper_bound {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) (z : Box n → ℝ)
    (hz : reservationIndices M multiplier z) (π : Policy n) :
    value M multiplier π ≤
      ∫ ω : Outcome n, fullInformationPayoff (fun i => min (ω.1 i) (z i)) ∂jointLaw M := by sorry
