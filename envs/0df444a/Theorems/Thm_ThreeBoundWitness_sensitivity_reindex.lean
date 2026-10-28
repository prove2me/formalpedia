-- Prove2me | Theorems.Thm_ThreeBoundWitness_sensitivity_reindex
-- name    : ThreeBoundWitness.sensitivity_reindex
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:39:37.233992+00:00
-- url     : https://prove2.me/theorems/ce67a36b-3bfb-4db2-8149-823f493e5ddf
-- title:
--   Sensitivity is invariant under a bijection of input coordinates
-- statement:
--   Let \(I,J\) be finite coordinate types, let \(e:I\cong J\) be a bijection, and let \(f:\{0,1\}^{I}\to\{0,1\}\). Reindex \(f\) along \(e\) to obtain a function on \(J\). Then
--   \[
--   s(\operatorname{reindex}_e f)=s(f).
--   \]
--   This permits recursive functions on structured finite coordinate types to be presented on \(\operatorname{Fin}(n)\).
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, WitnessLifting, lines 385–399; source SHA256 3de5b42744f1a0f912bff6a7825dc8a21c88ce1eeb9e3364123000d6bca68bcc.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ThreeBoundWitness
end ThreeBoundWitness
open ThreeBoundWitness
open OAI.Paper320
variable {L I V : Type}

theorem ThreeBoundWitness.sensitivity_reindex {J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (reindex e f) = sensitivity f := by sorry
