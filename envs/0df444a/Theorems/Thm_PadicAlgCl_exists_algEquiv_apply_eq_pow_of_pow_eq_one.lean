-- Prove2me | Theorems.Thm_PadicAlgCl_exists_algEquiv_apply_eq_pow_of_pow_eq_one
-- name    : PadicAlgCl.exists_algEquiv_apply_eq_pow_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/cd3b7847-63cc-57e7-81ff-5baf58865045
-- title:
--   A Frobenius element raising (p^N-1)-st roots of unity to the p-th power
-- statement:
--   Let $p$ be a prime and let $N$ be a natural number with $0 < N$. The assertion is that there exists a $\mathbb{Q}_p$-algebra automorphism $\varphi$ of the fixed algebraic closure `PadicAlgCl p` of $\mathbb{Q}_p$ — that is, an element of $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ in the guise of a term of type `PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p` — with the property that for every $w \in \overline{\mathbb{Q}}_p$ satisfying $w^{p^N-1} = 1$ one has $\varphi(w) = w^p$. Thus $\varphi$ acts on the group of roots of unity of order dividing $p^N - 1$ exactly as the $p$-power map; no condition is imposed on its behaviour elsewhere, and $N$ enters only through the exponent $p^N - 1$. The hypothesis $0 < N$ is what makes $p^N - 1$ positive, so that the condition $w^{p^N-1} = 1$ cuts out a genuine finite group of roots of unity.
--
--   This produces an arithmetic Frobenius for the unramified extension $\mathbb{Q}_p(\mu_{p^N-1})/\mathbb{Q}_p$, extended to a global automorphism of $\overline{\mathbb{Q}}_p$; its residue degree is $1$ because the base field is $\mathbb{Q}_p$ itself. It is used in the local analysis of deformations and levels at $p$, being cited by [`PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening`](thm.html#PadicAlgCl.exists_isUnit_forall_dvd_valuation_of_thickening), [`PadicAlgCl.exists_unramified_level_char_of_sq_sub_one_mem_span_socle`](thm.html#PadicAlgCl.exists_unramified_level_char_of_sq_sub_one_mem_span_socle) and [`NumberField.PlaceDecomp.inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2`](thm.html#NumberField.PlaceDecomp.inflate_sub_unitsInflate2_carryFun_mem_levelCoboundaries2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_exists_algEquiv_apply_eq_pow_of_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.exists_algEquiv_apply_eq_pow_of_pow_eq_one (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    ∃ φ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ∀ w : PadicAlgCl p, w ^ (p ^ N - 1) = 1 → φ w = w ^ p := by sorry
