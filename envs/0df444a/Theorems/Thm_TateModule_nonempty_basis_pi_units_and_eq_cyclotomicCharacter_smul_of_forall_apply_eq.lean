-- Prove2me | Theorems.Thm_TateModule_nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq
-- name    : TateModule.nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/be25ca1d-f88c-5d1f-99b6-b2f19d16de6f
-- title:
--   Tate module of a split torus: freeness and cyclotomic character
-- statement:
--   Let $p$ be a prime, let $L$ be a field such that for every $i\in\mathbb N$ the group $\mu_{p^i}(L)$ has the expected size (the instance `HasEnoughRootsOfUnity L (p ^ i)` for all $i$), and let $\iota$ be a finite type. Write $M=\iota\to\operatorname{Additive}L^\times$ and let $T=$ [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) be the additive subgroup of sequences $x:\mathbb N\to M$ satisfying $p^n\cdot x_n=0$ and $p\cdot x_{n+1}=x_n$ for all $n$, regarded as a $\mathbb Z_p$-module. The theorem asserts two things. First, $T$ admits a $\mathbb Z_p$-basis indexed by $\iota$ itself, i.e. `Module.Basis ι ℤ_[p] T` is nonempty; in particular $T$ is free of rank $|\iota|$. Second, for every ring automorphism $\sigma$ of $L$ (an element of $L\simeq_{+*}L$) and all $s,t\in T$, if at every level $v\in\mathbb N$ and every coordinate $i\in\iota$ the unit underlying $s_v(i)$ equals $\sigma$ applied to the unit underlying $t_v(i)$ in $L$, then $s=\chi(\sigma)\cdot t$, where $\chi(\sigma)=$ `cyclotomicCharacter L p σ` is viewed in $\mathbb Z_p^\times$ and then in $\mathbb Z_p$ acting by scalar multiplication on $T$.
--
--   This is the basic computation $T_p(\mathbb G_m^\iota)\cong\mathbb Z_p(1)^{\iota}$: the $p$-adic Tate module of the $L$-points of a split torus is free of rank equal to the rank of the torus, and automorphisms of $L$ act on it by the homothety given by the $p$-adic cyclotomic character. It is used in the treatment of Cartier duality for $p$-divisible groups, where the Tate module of $\mathbb G_m$ supplies the target of the duality pairing and hence the cyclotomic twist in the resulting Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.nonempty_basis_pi_units_and_eq_cyclotomicCharacter_smul_of_forall_apply_eq
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [∀ i : ℕ, HasEnoughRootsOfUnity L (p ^ i)]
    (ι : Type) [Finite ι] :
    Nonempty (Module.Basis ι ℤ_[p] (TateModule p (ι → Additive Lˣ))) ∧
    ∀ (σ : L ≃+* L) (s t : TateModule p (ι → Additive Lˣ)),
      (∀ (v : ℕ) (i : ι), ((Additive.toMul ((s : ℕ → ι → Additive Lˣ) v i) : Lˣ) : L) =
          σ (((Additive.toMul ((t : ℕ → ι → Additive Lˣ) v i) : Lˣ) : L))) →
      s = ((cyclotomicCharacter L p σ : ℤ_[p]ˣ) : ℤ_[p]) • t := by sorry
