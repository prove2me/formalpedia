-- Prove2me | Theorems.Thm_StrongConv_supp_subset_Icc_limsup
-- name    : StrongConv.supp_subset_Icc_limsup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:41:44.31921+00:00
-- url     : https://prove2.me/theorems/930e8485-3dff-42e7-a53b-199ac0609c9c
-- title:
--   Lemma 4.9 — the support of a distribution is bounded by the growth of its moments
-- statement:
--   For every compactly supported distribution $\nu$ (Definition 4.6), $\operatorname{supp}\nu \subseteq [-\rho, \rho]$, where $\rho = \limsup_{p\to\infty} |\nu(x^p)|^{1/p}$, the limit superior of a sequence of real numbers.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 18, Lemma 4.9, which applies Estrada, R. and Kanwal, R. P., Moment sequences for a certain class of distributions, Complex Variables Theory Appl. 9 (1987) 31–39, Lemma 1, https://doi.org/10.1080/17476938708814247, or Schultz, H., Non-commutative polynomials of independent Gaussian random matrices. The real and symplectic cases, Probab. Theory Related Fields 131 (2005) 261–309, Theorem 5.4, https://doi.org/10.1007/s00440-004-0366-7

import Mathlib
import Definitions.Def_StrongConv

open Filter Polynomial

namespace StrongConv

theorem supp_subset_Icc_limsup (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) :
    supp ν ⊆ Set.Icc (-limsup (fun p : ℕ => |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop)
      (limsup (fun p : ℕ => |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop) := by
  sorry

end StrongConv
