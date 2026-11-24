-- Prove2me | Theorems.Thm_SensitivityLocalNumeric_phase0_jcert_6_7_9
-- name    : SensitivityLocalNumeric.phase0_jcert_6_7_9
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:49:00.279816+00:00
-- url     : https://prove2.me/theorems/ab87439d-3c7b-430f-a96a-d8e3f9637921
-- title:
--   Unary joint-event certificate at ranks $(6,7,9)$
-- statement:
--   Fix the rank triple $(c,x,n)=(6,7,9)$ for the unary Paley recipe. Let $v$ be the checkpoint input bounds, $w$ the first image profile, $P=P_0(x,n)$ the stored promotion bound, and $J=J_0(c,x,n)$ the stored joint bound. All three components of the joint certificate hold:
--
--   $$Q_{\rm cost}(6,7,9;P,J)=Q_{\rm interval}(6,7,9)=Q_{\rm cold}(6,7,9)=\mathrm{true}.$$
--
--   The cost check establishes either $M_w(c,x)+P\le J$, or $M_w(c,x)\le J$ together with a bound of $J$ on every relevant enumerated joint-event fee. The interval check covers all affected own and guard transitions, and the cold-endpoint check places the empty-guard cutoff above the required soft threshold. These are the finite obligations used to transport joint-event bounds through the unary stage.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/LocalNumericChecks/Phase0J06.lean lines 20–21; SHA256 8fccc57bf5e09b71306ae90dfe0552bf8a51210604e3c342da52958e91eddab6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LiteralProfileData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericCertificatesCore
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

namespace SensitivityLocalNumeric
end SensitivityLocalNumeric


open SensitivityLocalNumeric
set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option Elab.async false

theorem SensitivityLocalNumeric.phase0_jcert_6_7_9 :
    JointCertified phase0 input0 SensitivityLiteralRay.image0Data 6 7 9 (p0 7 9) (j0 6 7 9) := by sorry
