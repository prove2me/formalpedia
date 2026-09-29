-- Prove2me | Theorems.Thm_PadicInt_exists_forall_apply_eq_pow_smul_imp_exists_eq_smul_of_injective
-- name    : PadicInt.exists_forall_apply_eq_pow_smul_imp_exists_eq_smul_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/6a1d2e5d-cb3a-594c-afd9-85ce6bd9f390
-- title:
--   Uniform depth at which an injective additive map detects p-divisibility
-- statement:
--   Let $p$ be a natural number which is assumed prime, let $n$ be a natural number, and let $f$ be an additive group homomorphism from $\mathbb{Z}_p^n = (\mathrm{Fin}\ n \to \mathbb{Z}_p)$ to itself, assumed injective as a function. The assertion is that there exists a natural number $M$ with the following property: for all $w, y \in \mathbb{Z}_p^n$, if $f(w) = p^{M} \cdot y$, where $p^{M}$ acts by scalar multiplication through the image of $p$ in $\mathbb{Z}_p$, then there exists $v \in \mathbb{Z}_p^n$ with $w = p \cdot v$. Equivalently, a single exponent $M$, depending on $f$ alone and not on $w$ or $y$, suffices so that $f^{-1}\big(p^{M}\mathbb{Z}_p^n\big) \subseteq p\,\mathbb{Z}_p^n$. Note that $f$ is only assumed additive, not a priori $\mathbb{Z}_p$-linear, and that $n = 0$ is allowed.
--
--   This is the uniform-depth form of the elementary fact that an injective endomorphism of the lattice $\mathbb{Z}_p^n$ has bounded index image, so that membership of $f(w)$ in a sufficiently deep congruence subgroup forces $w \equiv 0 \bmod p$. It is used in the Čerednik–Drinfeld part of the development, in the lemma on rigidified special formal modules [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_forall_apply_eq_pow_smul_imp_exists_eq_smul_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicInt.exists_forall_apply_eq_pow_smul_imp_exists_eq_smul_of_injective
    (p : ℕ) [Fact p.Prime] {n : ℕ}
    (f : (Fin n → ℤ_[p]) →+ (Fin n → ℤ_[p])) (hf : Function.Injective f) :
    ∃ M : ℕ, ∀ (w y : Fin n → ℤ_[p]), f w = ((p : ℤ_[p]) ^ M) • y →
      ∃ v : Fin n → ℤ_[p], w = (p : ℤ_[p]) • v := by sorry
