-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_gittins_capped_reward_identity
-- name    : PandoraBO.Private20261023.gittins_capped_reward_identity
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:05:32.087368+00:00
-- url     : https://prove2.me/theorems/45cb7797-9d53-41d6-b270-03011a1f2b15
-- title:
--   A Gittins policy attains the capped-reward bound
-- statement:
--   For reservation indices at a strictly positive multiplier, the penalized value of every Gittins policy equals the expected maximum of the box rewards capped at those indices. The statement includes randomized tie rules and the mandatory first opening in the model.
-- source:
--   Capped-reward proof of Weitzman’s rule used in Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5, Lemma 7 Part I, equation (42), citing Kleinberg et al., Theorem 1. The inequality and equality cases are separated for the formalization.

import Definitions.Def_PandoraBO_Model
open MeasureTheory PandoraBO
set_option autoImplicit false

theorem PandoraBO.Private20261023.gittins_capped_reward_identity {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) (z : Box n → ℝ)
    (hz : reservationIndices M multiplier z) (π : Policy n)
    (hπ : isGittinsPolicy M multiplier π) :
    value M multiplier π =
      ∫ ω : Outcome n, fullInformationPayoff (fun i => min (ω.1 i) (z i)) ∂jointLaw M := by sorry
