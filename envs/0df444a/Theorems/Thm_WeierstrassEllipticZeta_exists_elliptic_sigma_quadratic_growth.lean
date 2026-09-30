-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_quadratic_growth
-- name    : WeierstrassEllipticZeta.exists_elliptic_sigma_quadratic_growth
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T22:20:28.583548+00:00
-- url     : https://prove2.me/theorems/155c2a1f-8159-4ff8-af08-40d38dd677dc
-- title:
--   Finite quadratic exponential growth of normalized sigma
-- statement:
--   For every complex period pair $L$, with lattice $\Lambda$ and canonical zeta function $\zeta_L$, there exist an entire function $\sigma:\mathbb C\to\mathbb C$ and a real constant $A>0$ such that
--
--   $$\sigma(0)=0,\qquad \sigma'(0)=1,\qquad
--   \sigma'(z)=\zeta_L(z)\sigma(z)\quad(z\notin\Lambda),$$
--
--   and
--
--   $$|\sigma(z)|\le \exp\bigl(A(1+|z|^2)\bigr)
--   \qquad(z\in\mathbb C).$$
--
--   The constant depends only on the period pair. The estimate is global, including the lattice and the origin. It is a finite quadratic exponential bound, stronger than merely asserting entire-function order at most two. This is the quantitative sigma input used before Kumar's Lemma 6; the existence of a normalized entire sigma differential solution without this estimate is already proved in the mission.
-- source:
--   Senthil Kumar K (2026), Section 4, finite quadratic exponential bound immediately before Lemma 6, https://doi.org/10.1017/S001309152610145X. Classical sigma quasi-periodicity: DLMF 23.2.15 and 23.2.17, https://dlmf.nist.gov/23.2#E15. The global bound with 1+|z|² also absorbs the compact disk.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.exists_elliptic_sigma_quadratic_growth
    (L : PeriodPair) :
    ∃ (D : EllipticSigmaDifferentialData L) (A : ℝ), 0 < A ∧
      ∀ z : ℂ, ‖D.sigma z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)) := by sorry
