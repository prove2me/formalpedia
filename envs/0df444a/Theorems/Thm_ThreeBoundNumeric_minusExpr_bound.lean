-- Prove2me | Theorems.Thm_ThreeBoundNumeric_minusExpr_bound
-- name    : ThreeBoundNumeric.minusExpr_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:39:47.783144+00:00
-- url     : https://prove2.me/theorems/4acd2ad9-5ed8-43ca-8442-dc2be3e5c151
-- title:
--   Adjacent boundary maxima control a nonadjacent mixed profile
-- statement:
--   Let \(F\) be a Boolean family indexed by \(\operatorname{Fin}(n)\), and let \(v\) upper-bound all of its stored profiles. For indices \(i\le j<k\), the mixed profile across the interval from \(j\) to \(k\) satisfies
--   \[
--   M_F(i,j,k)\le \operatorname{minusExpr}(n,i,j,k)[v].
--   \]
--   The expression on the right is the maximum of the stored adjacent-boundary \(M\)-coordinates over that interval. This permits transfers to use nonadjacent levels without storing every such profile separately.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ProfileIntervals, lines 52–65; source SHA256 d459359ece9a5eb9b94eebb512c181956cf125c4577048018b0a8a4b66a1a2e9.

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

theorem ThreeBoundNumeric.minusExpr_bound (F : Fin n → (I → Bool) → Bool) (v : Profile n)
    (hv : Upper F v) (i j k : Fin n) (hij : i ≤ j) (hjk : j < k) :
    MBound F i j k ((minusExpr n i.val j.val k.val).eval v) := by sorry
