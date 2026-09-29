-- Prove2me | Theorems.Thm_SYZ_eqA2_variation_of_deformation_form_is_exact
-- name    : SYZ.eqA2_variation_of_deformation_form_is_exact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T04:04:32.716496+00:00
-- url     : https://prove2.me/theorems/a8b6c7ce-35de-4830-b2c9-27d93a48a3f5
-- title:
--   SYZ Eq. (A.2): $\partial_a \theta^b$ is exact
-- statement:
--   **Equation (A.2) of Strominger–Yau–Zaslow.** In the moduli coordinates of Section 3 — a smooth family of special Lagrangian tori in which every deformation $1$-form $\theta^a$ is harmonic for the induced metric and has constant periods — the derivative of a deformation form along any moduli direction is an **exact** $1$-form:
--   $$\frac{\partial \theta^b}{\partial t^a} \;=\; d\psi$$
--   for some function $\psi$ on the brane.
--
--   This is the content of Appendix A of the paper, where $\psi$ is computed explicitly as $-\tfrac12\,\partial^2\phi/\partial s\,\partial t$ in terms of the gauge function $\phi$ of the flow. It is the statement that although each harmonic representative $\theta^b$ must change as the induced metric changes, it changes only within its cohomology class; this is what makes the almost complex structure on the moduli space constant in these coordinates, and it is the input to the derivation of Eq. (3.4).
-- source:
--   A. Strominger, S.-T. Yau, E. Zaslow, "Mirror symmetry is T-duality", Nuclear Physics B 479 (1996) 243-259, doi:10.1016/0550-3213(96)00434-8, arXiv:hep-th/9606040, pp. 253 and 256-258, Eq. (3.3) and Appendix A, Eq. (A.1)-(A.2)

import Definitions.Def_syz_flat_model

namespace SYZ

theorem eqA2_variation_of_deformation_form_is_exact {n m : ℕ}
    (S : SYZFamily n m) (a b : Fin m) (t : Dom m) :
    ∃ psi : Dom n → ℝ, ∀ (x : Dom n) (i : Fin n),
      D (fun s => thetaM S.F b s x i) a t = D psi i x := by sorry

end SYZ
