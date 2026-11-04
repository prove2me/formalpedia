-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_naturalDot_rowMenu
-- name    : ThreeSum.TernaryExtensionEncoding.naturalDot_rowMenu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:19.526136+00:00
-- url     : https://prove2.me/theorems/76b52463-f1b0-4d34-82a2-5e57a38a9dbc
-- title:
--   Ternary Extension Encoding: natural Dot row Menu
-- statement:
--   The Ternary Extension Encoding construction uses the natural Dot row Menu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L112-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L112-L132

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] ThreeSum.TernaryExtensionEncoding._p2m_local_instance_7138b7e7ca_12
variable {f : (ZMod p)[X]}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]

theorem ThreeSum.TernaryExtensionEncoding.naturalDot_rowMenu (hf : f.Monic) (hd : 0<f.natDegree) (Λ : ℕ)
    (x y : AdjoinRoot f) (raw : Fin Λ → ℤ)
    (values coefs : ℕ → ℕ)
    (hvalues : ∀ i : Fin Λ, (values i.val : ZMod p)=(raw i : ZMod p))
    (hcoefs : ∀ i : Fin Λ, coefs i.val=
      LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i.val%p) :
    LightNaturalDot.dot values coefs Λ%p=
      (TernaryOriginalRowMenu.row Λ (constantCoefficient hf hd) (x,y)
        (fun i => (raw i : ZMod p))).val := by sorry
