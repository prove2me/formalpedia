-- Prove2me | Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
-- name    : PadicAlgCl.isIntegral_padicInt_iff_norm_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/fa41abf7-8251-5845-a746-b57b21b0f57a
-- title:
--   Integrality over ℤₚ in ℚ̄ₚ is equivalent to ‖x‖≤ 1
-- statement:
--   Let $p$ be a prime number and let `PadicAlgCl p` be the algebraic closure $\overline{\mathbb{Q}}_p$ of $\mathbb{Q}_p$, carrying its canonical norm (the unique absolute value extending the $p$-adic one, realised as the spectral norm of the extension $\overline{\mathbb{Q}}_p/\mathbb{Q}_p$). The theorem asserts that for every element $x$ of $\overline{\mathbb{Q}}_p$ the following two conditions are equivalent: $x$ is integral over the ring $\mathbb{Z}_p$ of $p$-adic integers, i.e. $x$ is a root of some monic polynomial with coefficients in $\mathbb{Z}_p$ (via the canonical algebra structure of $\overline{\mathbb{Q}}_p$ over $\mathbb{Z}_p$), and $\|x\| \le 1$. Thus the closed unit ball of $\overline{\mathbb{Q}}_p$ coincides with the integral closure of $\mathbb{Z}_p$ in $\overline{\mathbb{Q}}_p$; in particular, intersecting with a finite subextension $E/\mathbb{Q}_p$, the valuation ring $\{x \in E : \|x\| \le 1\}$ is the integral closure of $\mathbb{Z}_p$ in $E$.
--
--   This is the standard identification of the ring of integers of an algebraic extension of a complete discretely valued field with the unit ball of the extended absolute value. It is used throughout the local study of the $p$-adic Galois representations in the argument, for instance in the results on formally unramified algebras, inertia subgroups of $p$-adic integer rings and étale subextensions that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.isIntegral_padicInt_iff_norm_le_one (p : ℕ) [Fact p.Prime]
    (x : PadicAlgCl p) : IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 := by sorry
