-- Prove2me | Theorems.Thm_ThreeBoundNumeric_unionExpr_bound
-- name    : ThreeBoundNumeric.unionExpr_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:39:50.601026+00:00
-- url     : https://prove2.me/theorems/8f582750-68c4-493b-b1e6-9d0bb4e2cd36
-- title:
--   Adjacent boundary maxima control a nonadjacent union profile
-- statement:
--   Let \(v\) upper-bound the profiles of a Boolean family \(F\) indexed by \(\operatorname{Fin}(n)\). If \(i\le j<k\le l\), then
--   \[
--   D_F(i,j,k,l)\le \operatorname{unionExpr}(n,i,j,k,l)[v].
--   \]
--   Here the right-hand side is the maximum of the stored \(D\)-coordinates obtained by placing an adjacent true-to-false boundary between \(j\) and \(k\), while retaining endpoints \(i,l\). This supplies the interval union bounds used in shared-child repair costs.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ProfileIntervals, lines 81–95; source SHA256 d459359ece9a5eb9b94eebb512c181956cf125c4577048018b0a8a4b66a1a2e9.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures

namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundProfiles
end ThreeBoundProfiles
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ThreeBoundNumeric
end ThreeBoundNumeric
open ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile
variable {n : ℕ} {I : Type} [Fintype I]

theorem ThreeBoundNumeric.unionExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j k l : Fin n)
    (hij : i ≤ j) (hjk : j < k) (hkl : k ≤ l) :
    DBound F i j k l ((unionExpr n i.val j.val k.val l.val).eval v) := by sorry
