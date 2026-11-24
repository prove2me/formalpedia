-- Prove2me | Theorems.Thm_P2M_FairSelling_exists_threequarter_MMS_three_nobig__2b81d0860f2f
-- name    : P2M_FairSelling_exists_threequarter_MMS_three_nobig__2b81d0860f2f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:20.976526+00:00
-- url     : https://prove2.me/theorems/28d72c39-c666-41bd-b28d-12e4953c3dde
-- title:
--   P2 M Fair Selling exists threequarter MMS three nobig  2b81d0860f2f: P2 M Fair Selling exists threequarter MMS three nobig  2b81d0860f2f
-- statement:
--   **The `n = 3`, `3/4`-MMS theorem after the preliminary phase**, with no assumptions beyond the
--   absence of big goods.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean#L226-L231
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean#L226-L231

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem P2M_FairSelling_exists_threequarter_MMS_three_nobig__2b81d0860f2f (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry

alias «FairSelling».«exists_threequarter_MMS_three_nobig'» := P2M_FairSelling_exists_threequarter_MMS_three_nobig__2b81d0860f2f
