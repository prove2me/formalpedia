-- Prove2me | Theorems.Thm_PadicInt_exists_forall_exists_apply_eq_pow_smul_of_injective
-- name    : PadicInt.exists_forall_exists_apply_eq_pow_smul_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/76b85585-be85-5581-8d23-4930ae26b589
-- title:
--   Injective additive endomorphism of ℤₚⁿ contains p^Nℤₚⁿ
-- statement:
--   Let $p$ be a natural number, assumed prime, and let $n$ be a natural number. Let $f$ be an additive group homomorphism from $\mathbb{Z}_p^n$, realised as the functions $\mathrm{Fin}\,n \to \mathbb{Z}_p$ under pointwise addition, to itself, and suppose $f$ is injective as a map of sets. The conclusion is the existence of a natural number $N$ such that for every $v \in \mathbb{Z}_p^n$ there is some $w \in \mathbb{Z}_p^n$ with $f(w) = p^N \cdot v$, the scalar $p^N$ being the image of $p$ in $\mathbb{Z}_p$ raised to the $N$-th power and acting by the $\mathbb{Z}_p$-module structure. Equivalently: the image of an injective additive endomorphism of $\mathbb{Z}_p^n$ contains $p^N\mathbb{Z}_p^n$ for some $N$, with $N$ uniform in $v$ (the quantifier over $N$ precedes that over $v$). No $\mathbb{Z}_p$-linearity of $f$ is assumed; only additivity is hypothesised.
--
--   This is the standard statement that an injective endomorphism of a finite free $\mathbb{Z}_p$-module has image of finite index, in the concrete form that the image swallows a $p$-power multiple of the whole module; the point of the formulation is that mere additivity suffices, $\mathbb{Z}_p$-linearity being automatic. It serves as a lattice-index lemma, used in the Čerednik–Drinfel'd part of the development in [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed_uniform`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed_uniform) to obtain cofinality of base-changed $\eta$-lattices inside a rank-two $\mathbb{Z}_p$-module on a geometric fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_forall_exists_apply_eq_pow_smul_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt

theorem PadicInt.exists_forall_exists_apply_eq_pow_smul_of_injective
    (p : ℕ) [Fact p.Prime] {n : ℕ} (f : (Fin n → ℤ_[p]) →+ (Fin n → ℤ_[p])) (hf : Function.Injective f) :
    ∃ N : ℕ, ∀ v : Fin n → ℤ_[p], ∃ w : Fin n → ℤ_[p], f w = (p : ℤ_[p]) ^ N • v := by sorry
