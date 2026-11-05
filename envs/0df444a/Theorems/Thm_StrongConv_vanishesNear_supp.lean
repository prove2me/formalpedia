-- Prove2me | Theorems.Thm_StrongConv_vanishesNear_supp
-- name    : StrongConv.vanishesNear_supp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T00:05:08.703239+00:00
-- url     : https://prove2.me/theorems/34a53ee8-9e0e-457e-95b4-292d3c76ae0a
-- title:
--   A compactly supported distribution vanishes on functions that vanish near its support
-- statement:
--   Let $\nu$ be a compactly supported distribution (Definition 4.6, `StrongConv.IsCSDistribution`) and $\operatorname{supp}\nu$ its support (Definition 4.8, `StrongConv.supp`). Then $\nu(f) = 0$ for every $f \in C^\infty(\mathbb R)$ that vanishes in a neighborhood of $\operatorname{supp}\nu$ (`StrongConv.VanishesNear`).
--
--   Definition 4.8 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. (2) 203 (2026) 555–602 (arXiv v3, p. 18) defines the support as the smallest closed set $A$ with $\nu(f) = 0$ whenever $f$ vanishes in a neighborhood of $A$; that such a smallest set exists, and so that the support itself has this property, is the content of this statement. The proof of Theorem 3.14 (p. 32) uses it when $\nu_i(\chi) = 0$ is deduced from $\operatorname{supp}\nu_i \subseteq [-\rho, \rho]$ and $\chi = 0$ near $[-\rho, \rho]$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 18, Definition 4.8 (the support has the defining property)

import Mathlib
import Definitions.Def_StrongConv

open Polynomial Filter Topology

namespace StrongConv

theorem vanishesNear_supp (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) :
    VanishesNear ν (supp ν) := by
  sorry

end StrongConv
