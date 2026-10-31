-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P48_figureThreeValue
-- name    : QAlgorithms.Papers.Independent.Intake100.P48.figureThreeValue
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:26:29.842986+00:00
-- url     : https://prove2.me/theorems/c3cf2ede-deae-4223-9885-14222db54759
-- title:
--   Conditional topology-dependent entropy in Fig. 3
-- statement:
--   At common scale $t>0$, take planar rectangles $A=t([0,1]\times[0,3])$, $C=t([2,3]\times[0,3])$, and $B=t([1,2]\times[0,1])\cup t([1,2]\times[2,3])$. The central open square belongs to the exterior, so $ABC$ is an annulus. For every nonempty union $U$ let $L_U=\mathcal H^1(\partial U)$ and let $b_U$ be the number of connected components of its boundary. Fix $\alpha\in\mathbb R$ and $\gamma\ge0$, and define the conditional effective entropy $S(U)=\alpha L_U-\gamma b_U$.
--
--   Every boundary has finite length and finitely many components. In the order $A,B,C,AB,BC,AC,ABC$ the component counts are $(1,2,1,1,1,2,2)$, the alternating boundary-length sum is zero, and
--
--   $$
--   S(A)+S(B)+S(C)-S(AB)-S(BC)-S(AC)+S(ABC)=-2\gamma.
--   $$
--
--   This records the source's conditional application of one $-\gamma$ per boundary component to its actual topology.
-- source:
--   Topological entanglement entropy, arXiv:hep-th/0510092v2, PDF p. 4, Fig. 3 and text following Eq. (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P48

open Filter

open scoped Topology ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF p.4, Fig.3: B, AC and ABC each have two boundary components; the
other four unions have one. Length terms cancel on the actual shared interfaces.
This is the conditional effective calculation, not a microscopic area law. -/
theorem figureThreeValue (t alpha gamma : ℝ) (ht : 0 < t) (hgamma : 0 ≤ gamma) :
    (∀ u : Finset (Fin 3), u.Nonempty →
      MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (regionUnion (figureThreePiece t) u)) < ⊤ ∧
      Finite (ConnectedComponents (frontier (regionUnion (figureThreePiece t) u))) ∧
      boundaryCount (regionUnion (figureThreePiece t) u) =
        (if u = {1} ∨ u = {0, 2} ∨ u = {0, 1, 2} then 2 else 1)) ∧
    tripartite (fun u => boundaryLength (regionUnion (figureThreePiece t) u)) = 0 ∧
    tripartite (fun u => effectiveEntropy alpha gamma
      (regionUnion (figureThreePiece t) u)) = -2 * gamma := by sorry

end QAlgorithms.Papers.Independent.Intake100.P48

end
