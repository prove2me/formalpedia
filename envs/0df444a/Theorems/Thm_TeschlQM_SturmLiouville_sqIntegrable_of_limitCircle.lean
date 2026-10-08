-- Prove2me | Theorems.Thm_TeschlQM_SturmLiouville_sqIntegrable_of_limitCircle
-- name    : TeschlQM.SturmLiouville.sqIntegrable_of_limitCircle
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-10-04T19:57:08.293478+00:00
-- url     : https://prove2.me/theorems/06d0a753-f791-4755-bc9e-4affb6d19dc3
-- title:
--   Limit circle at $a$ implies all solutions are square integrable near $a$ for some $z_0$
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data. If $\tau$ is limit circle at $a$ (Wronskian definition, Teschl p. 187), then there is $z_0\in\mathbb C$ such that every solution of $(\tau-z_0)u=0$ is square integrable near $a$. Similarly at $b$.
--
--   In Teschl this follows from Theorem 9.6 and Lemma 9.7. Take two real $v,\tilde v\in\mathfrak D(\tau)$ with $W_a(v,\tilde v)\neq0$; they give two self-adjoint realizations. For nonreal $z$, the solutions $u_a$ and $\tilde u_a$ of Lemma 9.7 are square integrable near $a$ and linearly independent.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, Section 9.2, proof of Theorem 9.9 (p. 191), the 'only if' direction

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_IsLimitCircle
import Definitions.Def_TeschlQM_SturmLiouville_IsSqIntegrableNear

namespace TeschlQM.SturmLiouville

theorem sqIntegrable_of_limitCircle (L : SLData) :
    (IsLimitCircleLeft L →
      ∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearLeft L u) ∧
    (IsLimitCircleRight L →
      ∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearRight L u) := by sorry

end TeschlQM.SturmLiouville
