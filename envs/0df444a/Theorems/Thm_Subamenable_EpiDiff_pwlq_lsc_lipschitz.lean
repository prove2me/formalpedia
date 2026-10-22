-- Prove2me | Theorems.Thm_Subamenable_EpiDiff_pwlq_lsc_lipschitz
-- name    : Subamenable.EpiDiff.pwlq_lsc_lipschitz
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T23:48:14.936389+00:00
-- url     : https://prove2.me/theorems/2fd59edb-faa6-4611-b06d-6cf697f97353
-- title:
--   Convex PWLQ functions are l.s.c. and locally Lipschitz relative to their domain
-- statement:
--   Let $\vartheta:\mathbb R^m\to(-\infty,+\infty]$ be convex and piecewise linear-quadratic, i.e. $\operatorname{dom}\vartheta=\bigcup_{i=1}^s\Omega_i$ with polyhedral convex sets $\Omega_i$ and $\vartheta(y)=\tfrac12\langle A_iy,y\rangle+\langle a_i,y\rangle+\alpha_i$ on $\Omega_i$. Then
--
--   1. $\vartheta$ is lower semicontinuous at every point of $\mathbb R^m$;
--   2. for every $\bar y\in\operatorname{dom}\vartheta$ there are $\ell\ge0$ and a neighborhood $V$ of $\bar y$ with
--   $$|\vartheta(y)-\vartheta(z)|\le\ell\,\|y-z\|\qquad\text{for all }y,z\in V\cap\operatorname{dom}\vartheta,$$
--   i.e. $\vartheta$ is Lipschitz continuous around $\bar y$ relative to its domain.
--
--   These are the standing properties of the outer function used in Theorems 3.4 and 3.6 and in the proof of Theorem 5.2.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, p. 14 (remark after Theorem 3.6: the assumptions on the outer function of Theorem 3.6 hold for convex piecewise linear-quadratic functions) and p. 22 (proof of Theorem 5.2: "remember that θ is Lipschitz continuous relative to its domain")

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

namespace Subamenable.EpiDiff

theorem pwlq_lsc_lipschitz {m : ℕ} (theta : E m → EReal) (hconv : IsConvexPWLQ theta) :
    (∀ y : E m, LowerSemicontinuousAt theta y) ∧
      ∀ ybar ∈ dom theta, ∃ ell : ℝ, LipschitzRelativeAt theta ybar ell := by sorry

end Subamenable.EpiDiff
