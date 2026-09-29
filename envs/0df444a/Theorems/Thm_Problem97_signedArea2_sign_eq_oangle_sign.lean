-- Prove2me | Theorems.Thm_Problem97_signedArea2_sign_eq_oangle_sign
-- name    : Problem97.signedArea2_sign_eq_oangle_sign
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:01:45.275383+00:00
-- url     : https://prove2.me/theorems/604baa4f-359c-4c3b-872e-71ef00bed518
-- title:
--   Signed area and oriented angle have the same sign
-- statement:
--   Let $v,v_j,v_k$ be planar points with $v_j\ne v$ and $v_k\ne v$. The sign of the doubled signed area of $(v,v_j,v_k)$ is the sign of the standard counterclockwise oriented angle from $v_j-v$ to $v_k-v$. This bridge lets the proof translate between chord-side inequalities and angular order around an interior center.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_signedArea2_sign_eq_oangle_sign.lean#L1-L48

/- Generated theorem stub from Erdos9796Proof.P97.SignedAreaOangle by Stage 2 proof cut; source SHA-256 b3d7d5da8bb313997dd505e15b0ba2823db075ab8d863e995246ecbcce8f4fa9 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_SignedAreaOangle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
open Problem97



/-!
# Bridge: algebraic `signedArea2` ↔ Mathlib oriented angle sign

This module supplies the foundational bridge consumed by the MEC arc–angle
chain (sub-obligation `p97-signed-area-eq-oangle-sign`, alias A.1). The
algebraic predicate `Problem97.signedArea2` defined in `Foundation` is the
chord-side / signed-area form used by the cap-witness machinery. The MEC
parametrization, in contrast, needs Mathlib's oriented angle
`Orientation.oangle` on the standard counter-clockwise orientation of
`ℝ² = EuclideanSpace ℝ (Fin 2)`. Both quantities carry the *same sign* by a
direct computation: `signedArea2` is exactly the area form of the standard
orientation evaluated on the two chord vectors, and `oangle` is the
`Complex.arg` of the Kähler form whose imaginary part is that area form.

The single externally-used result is `signedArea2_sign_eq_oangle_sign`
(plus its `Real.sign` cast variant). All proofs are by direct Mathlib
manipulation; no new axioms are introduced.
-/

open scoped EuclideanGeometry

theorem Problem97.signedArea2_sign_eq_oangle_sign
    (v vj vk : ℝ²) (hj : vj ≠ v) (hk : vk ≠ v) :
    SignType.sign (Problem97.signedArea2 v vj vk) =
      (stdOrientation.oangle (vj - v) (vk - v)).sign := by sorry
