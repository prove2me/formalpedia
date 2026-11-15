-- Prove2me | Theorems.Thm_ResultantVNP_quadratic_to_tensor_circuits
-- name    : ResultantVNP.quadratic_to_tensor_circuits
-- status  : Proved
-- author  : @gjindal
-- created : 2026-11-14T08:43:51.559582+00:00
-- url     : https://prove2.me/theorems/b947833c-6954-4f04-aae2-7a7d0d985b32
-- title:
--   Polynomial-size resultant circuits give polynomial-size tensor determinant circuits
-- statement:
--   For an arbitrary resultant system, suppose the resultants of n homogeneous quadratic forms in n variables have arithmetic circuits over $\mathbb C$ of size polynomial in n. Then the general cubic tensor determinants also have polynomial-size arithmetic circuits.
--
--   The tensor determinant is obtained by substituting the coefficients of $(A x^2)_i=\sum_{j,k}a_{ijk}x_jx_k$ into the quadratic resultant. Each substituted coefficient is $a_{ijj}$ or $a_{ijk}+a_{ikj}$. The claim includes the circuit-size preservation for the mission's fan-in-two straight-line programs, where size counts gates rather than leaves.
--
--   This is a supporting circuit-specialization claim extracted from the paper's resultant-to-tensor specialization, not a separately numbered theorem in the paper.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission #1103, Definition 2.7, p.13, and the linear coefficient specialization in the proof of algebraic hardness, p.17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1103.pdf

import Mathlib
import Definitions.Def_ResultantVNP_quadRes
import Definitions.Def_ResultantVNP_tensorDet
import Definitions.Def_ResultantVNP_HasPolySizeCircuits

namespace ResultantVNP

theorem quadratic_to_tensor_circuits (𝓡 : ResultantSystem)
    (h : HasPolySizeCircuits
      (fun n => MvPolynomial.map (Int.castRingHom ℂ) (quadRes 𝓡 n))) :
    HasPolySizeCircuits
      (fun n => MvPolynomial.map (Int.castRingHom ℂ) (tensorDet 𝓡 n)) := by
  sorry

end ResultantVNP
