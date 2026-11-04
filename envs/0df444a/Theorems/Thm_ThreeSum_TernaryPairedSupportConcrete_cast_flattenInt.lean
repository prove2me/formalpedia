-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupportConcrete_cast_flattenInt
-- name    : ThreeSum.TernaryPairedSupportConcrete.cast_flattenInt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:46.231835+00:00
-- url     : https://prove2.me/theorems/c955d43e-e0e9-430c-be36-7470b95e3180
-- title:
--   Ternary Paired Support Concrete: cast flatten Int
-- statement:
--   The Ternary Paired Support Concrete construction uses the cast flatten Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean#L42-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean#L42-L48

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupportConcrete
open Finset TernaryPairedPotential TernaryPairedSupport
open scoped BigOperators
variable {K : Type*} [Field K]

theorem ThreeSum.TernaryPairedSupportConcrete.cast_flattenInt (J : ℕ) (u : (Fin J → ℤ) × (ℤ × ℤ)) :
    (fun i => (flattenInt J u i : K)) =
      flatten J ((fun j => (u.1 j : K)),((u.2.1 : K),(u.2.2 : K))) := by sorry
