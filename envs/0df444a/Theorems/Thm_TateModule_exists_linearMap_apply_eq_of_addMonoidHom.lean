-- Prove2me | Theorems.Thm_TateModule_exists_linearMap_apply_eq_of_addMonoidHom
-- name    : TateModule.exists_linearMap_apply_eq_of_addMonoidHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/dfa4a18f-38e5-5670-9cca-25d1da811b68
-- title:
--   Functoriality of the p-adic Tate module in M
-- statement:
--   Let $p$ be a prime and let $M$, $M'$ be additive commutative groups, and let $f \colon M \to M'$ be an additive homomorphism. For an additive commutative group $M$, the project's $p$-adic Tate module [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) is the subgroup of sequences $x \colon \mathbb{N} \to M$ such that for every $n$ one has $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ (integer scalar multiples), carrying its $\mathbb{Z}_p$-module structure, in which $a \in \mathbb{Z}_p$ acts levelwise through the integer approximations $a.\mathrm{appr}\,n$ of $a$. The assertion is that there exists a $\mathbb{Z}_p$-linear map $e \colon$ [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) $\to$ [`TateModule p M'`](def/EllipticCurve_TateModule.html#L15) with two properties: first, $e$ acts levelwise by $f$, that is, for every $x$ in [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) and every $n \in \mathbb{N}$ the $n$-th component of the sequence underlying $e(x)$ equals $f(x_n)$, where $x_n$ is the $n$-th component of the sequence underlying $x$; second, if $f$ is injective then $e$ is injective. Only the existence of such an $e$ is asserted, not its uniqueness (which would in any case follow from the levelwise description).
--
--   This is the functoriality of the $p$-adic Tate module $T_p(-) = \varprojlim_n (-)[p^n]$ in the coefficient group, in the form used throughout the project to transport Tate modules along maps of abelian groups. It is invoked where Tate modules of Jacobians and of $p$-divisible groups are compared, for instance in the passage from an additive isomorphism to an isomorphism of rational Tate modules compatible with Galois representations, and in the construction of Tate modules attached to $J_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_exists_linearMap_apply_eq_of_addMonoidHom.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.exists_linearMap_apply_eq_of_addMonoidHom
    (p : ℕ) [Fact p.Prime] {M M' : Type} [AddCommGroup M] [AddCommGroup M'] (f : M →+ M') :
    ∃ e : TateModule p M →ₗ[ℤ_[p]] TateModule p M',
      (∀ (x : TateModule p M) (n : ℕ), ((e x : TateModule p M') : ℕ → M') n = f ((x : ℕ → M) n)) ∧
      (Function.Injective f → Function.Injective e) := by sorry
