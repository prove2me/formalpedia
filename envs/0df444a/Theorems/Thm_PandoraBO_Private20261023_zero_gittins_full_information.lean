-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_zero_gittins_full_information
-- name    : PandoraBO.Private20261023.zero_gittins_full_information
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:18:13.023001+00:00
-- url     : https://prove2.me/theorems/9e9df710-2c79-466d-b3ca-77c5d5764d0b
-- title:
--   Every zero-index Gittins policy attains the full-information reward
-- statement:
--   Every policy obeying the zero-multiplier Gittins rule has expected reward equal to the full-information reward and is optimal at zero multiplier. This does not assert that every zero-index tie-breaking rule satisfies a particular budget.
-- source:
--   Auxiliary result supporting the zero-multiplier branch in Xie et al., author revised manuscript reviewed 23 October 2026, Appendix B.5.

import Definitions.Def_PandoraBO_Model
set_option autoImplicit false

theorem PandoraBO.Private20261023.zero_gittins_full_information {n : ℕ} (M : PandoraBO.Instance n) (π : PandoraBO.Policy n)
    (hπ : PandoraBO.isZeroGittinsPolicy M π) :
    PandoraBO.expectedReward M π = PandoraBO.fullInformationReward M ∧
    PandoraBO.optimal M 0 π  := by sorry
