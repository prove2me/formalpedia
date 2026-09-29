-- Prove2me | Theorems.Thm_WeinbergLeptons_eq9_wMass
-- name    : WeinbergLeptons.eq9_wMass
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:42:30.960087+00:00
-- url     : https://prove2.me/theorems/f1257a2f-8c85-4fd4-8d39-89b83c1901f8
-- title:
--   Eqs. (8)–(9): the charged boson $W$ has mass $M_W=\frac12\lambda g$
-- statement:
--   For all real $g,g',\lambda$, the coefficient vector $w=2^{-1/2}(1,i,0,0)$ of the charged field $W_\mu=2^{-1/2}(A_\mu^1+iA_\mu^2)$ is an eigenvector of the mass-squared matrix:
--
--   $$\mathcal M\,w=M_W^2\,w,\qquad M_W=\tfrac12\lambda g.$$
-- source:
--   S. Weinberg, A Model of Leptons, Phys. Rev. Lett. 19, 1264-1266 (1967), https://doi.org/10.1103/PhysRevLett.19.1264, p. 1265, eqs. (8), (9)

import Definitions.Def_WeinbergLeptons_Model

open Matrix

namespace WeinbergLeptons

theorem eq9_wMass (g g' lam : ℝ) :
    (massSqMatrix g g' lam).map (fun x : ℝ => (x : ℂ)) *ᵥ wVec = ((wMass g lam : ℂ) ^ 2) • wVec := by sorry

end WeinbergLeptons
