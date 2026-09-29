-- Prove2me | Theorems.Thm_VectorCalculus_angleField_not_conservative
-- name    : VectorCalculus.angleField_not_conservative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T00:26:26.675189+00:00
-- url     : https://prove2.me/theorems/f20c0f7b-236b-4fc2-ac45-8575d59c29f0
-- title:
--   The angle field is not conservative on the plane
-- statement:
--   The planar field $\mathbf F = \bigl(-y/(x^2+y^2),\ x/(x^2+y^2)\bigr)$ is not conservative: there is no continuous scalar field $\phi$, defined at every point of the plane, with $\mathbf F = \nabla\phi$. The candidate potential $\phi = \tan^{-1}(y/x)$ fails to be a continuous function on the plane, and the circulation $2\pi$ around any circle about the origin rules out every other candidate as well.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3.4 (pp. 25–26): "the deal is that $\phi(x,y)$ is not a well behaved function on $\mathbb R^2$ ... strictly speaking, a conservative field should have $\mathbf F = \nabla\phi$ with $\phi$ continuous"

import Definitions.Def_VectorCalculus_conservative
import Definitions.Def_VectorCalculus_angleField

namespace VectorCalculus

theorem angleField_not_conservative : ¬ IsConservative angleField := by sorry

end VectorCalculus
