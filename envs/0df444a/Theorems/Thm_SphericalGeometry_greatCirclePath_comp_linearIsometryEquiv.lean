-- Prove2me | Theorems.Thm_SphericalGeometry_greatCirclePath_comp_linearIsometryEquiv
-- name    : SphericalGeometry.greatCirclePath_comp_linearIsometryEquiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T11:17:41.566812+00:00
-- url     : https://prove2.me/theorems/d6b92003-cc91-4711-ab97-8c31129c20c2
-- title:
--   A linear isometry transports a great circle to the transported frame's circle
-- statement:
--   A linear isometry carries a great circle to the great circle of the transported frame:
--   $$w\bigl(\gamma_{v_1,v_2}(s)\bigr)=\gamma_{w v_1,\,w v_2}(s).$$
--
--   **Role.** The third of the three identities governing great circles and their frames. With the shift identity and the invariance of orthonormality, it reduces an equivariance condition $\gamma(s+T)=w\cdot\gamma(s)$ to an identity between two great circles named by explicit frames, and hence — the naming being determined by the frame — to equations for $w$ on the frame itself.
--
--   **Proof.** Immediate from additivity and $\mathbb R$-homogeneity of $w$.
-- source:
--   Elementary identity used in the closed-billiards-path analysis of Section 3 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem greatCirclePath_comp_linearIsometryEquiv {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (w : E ≃ₗᵢ[ℝ] E)
    (v1 v2 : E) (s : ℝ) :
    w (greatCirclePath v1 v2 s) = greatCirclePath (w v1) (w v2) s := by sorry

end SphericalGeometry
