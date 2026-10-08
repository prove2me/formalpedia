-- Prove2me | Theorems.Thm_TeschlQM_SturmLiouville_sqIntegrable_all_z
-- name    : TeschlQM.SturmLiouville.sqIntegrable_all_z
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-10-04T19:57:12.245153+00:00
-- url     : https://prove2.me/theorems/758b407e-7e38-42f9-8e90-7323f89fe891
-- title:
--   Square integrability of all solutions near an endpoint is independent of $z$
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data on $I=(a,b)$ and $\tau f = \frac1r(-(pf')'+qf)$. If for one $z_0\in\mathbb C$ every solution of $(\tau-z_0)u=0$ is square integrable near $a$ (i.e. $u\in L^2((a,c),r\,dx)$ for some $c\in I$), then for every $z\in\mathbb C$ every solution of $(\tau-z)u=0$ is square integrable near $a$. The same holds at the endpoint $b$.
--
--   This is the part of the proof of Weyl's alternative (Teschl, Thm. 9.9) showing that the property does not depend on $z$. It is proved by variation of constants: writing $(\tau - z_0)u = (z-z_0)u$, the Cauchy–Schwarz inequality on a sufficiently short interval $(a,c)$ gives an a-priori $L^2$ bound.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, Section 9.2, proof of Theorem 9.9 (p. 191) and Lemma 9.2

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_IsLimitCircle
import Definitions.Def_TeschlQM_SturmLiouville_IsSqIntegrableNear

namespace TeschlQM.SturmLiouville

theorem sqIntegrable_all_z (L : SLData) :
    ((∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearLeft L u) →
      ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearLeft L u) ∧
    ((∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearRight L u) →
      ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearRight L u) := by sorry

end TeschlQM.SturmLiouville
