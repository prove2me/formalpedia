-- Prove2me | Theorems.Thm_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul
-- name    : PadicComplex.exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/6ab0080e-fe16-5d28-af89-199502d38a55
-- title:
--   Bounded exponent for characters with a ℂₚ-period
-- statement:
--   Fix a prime $p$ and an intermediate field $K$ of $\mathbb{Q}_p \subseteq \overline{\mathbb{Q}}_p$, together with a monotone family $(K_m)_{m \in \mathbb{N}}$ of intermediate fields, each containing $K$ and each finite over $\mathbb{Q}_p$. Write $X$ for the closure in $\mathbb{C}_p$ of the union over $m$ of the images of the $K_m$. Assume given a real number $d$ and a level $m_0$ such that for every $m \ge m_0$ there is a map $R : \mathbb{C}_p \to \mathbb{C}_p$ which is additive on $X$, satisfies $R(kx) = kR(x)$ for $k \in K_m$ and $x \in X$, restricts to the identity on $K_m$, sends every element of $X$ into $K_m$, satisfies $R(\sigma \cdot x) = R(x)$ for all $x \in X$ and all $\sigma$ in the fixing subgroup of $K_m$, and satisfies Tate's estimate $\|x - R(x)\| \le d\,\|\sigma \cdot x - x\|$ for all $x \in X$ and all $\sigma$ fixing $K_m$ pointwise but not $K_{m+1}$. Let $L$ be a field, finite over $\mathbb{Q}_p$, and let $\psi$ be a group homomorphism from the fixing subgroup of $K$ to $L^{\times}$ which is trivial on those $\sigma$ lying in the fixing subgroup of every $K_m$. Suppose there is a non-zero $x \in \mathbb{C}_p \otimes_{\mathbb{Q}_p} L$ with $(\sigma \otimes \mathrm{id}_L)(x) = (1 \otimes \psi(\sigma)) \cdot x$ for every $\sigma$ in the fixing subgroup of $K$, the action on the left factor being the one induced by $\sigma$ on $\mathbb{C}_p$. Then there exists $n > 0$ with $\psi(\sigma)^n = 1$ for all such $\sigma$.
--
--   This is the cohomological half of Tate's computation that $H^0(\mathrm{Gal}(\overline{\mathbb{Q}}_p/K), \mathbb{C}_p(\chi))$ vanishes for a character $\chi$ of infinite order along a tower carrying normalised traces, stated here with coefficients in a finite extension $L$ of $\mathbb{Q}_p$ and with the conclusion in the form of a bounded exponent for the image of $\psi$ rather than mere finiteness. It is used in the proof of [`PadicComplex.eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul`](thm.html#PadicComplex.eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul), where the character in question is an integral power of the cyclotomic character, and thereby in the local analysis at $p$ of the Galois representations occurring in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul.lean

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicComplex_TateTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PadicComplex.exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
    (hK : ∀ m, K ≤ Km m) (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
    (d : ℝ) (m₀ : ℕ)
    (hR : ∀ m, m₀ ≤ m → ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R)
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ψ : K.fixingSubgroup →* Lˣ)
    (hψ' : ∀ σ : K.fixingSubgroup,
      (∀ m, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (Km m).fixingSubgroup) → ψ σ = 1)
    (x : ℂ_[p] ⊗[ℚ_[p]] L) (hx : x ≠ 0)
    (hψ : ∀ σ : K.fixingSubgroup,
      Algebra.TensorProduct.map
          (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (AlgHom.id ℚ_[p] L)
          x =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : Lˣ) : L)) * x) :
    ∃ n : ℕ, 0 < n ∧ ∀ σ : K.fixingSubgroup, ψ σ ^ n = 1 := by sorry
