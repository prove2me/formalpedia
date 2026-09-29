-- Prove2me | Theorems.Thm_TateModule_exists_linearMap_forall_apply_eq
-- name    : TateModule.exists_linearMap_forall_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/85dd98bd-bc7e-54a2-955f-6b53e700ead6
-- title:
--   Functoriality of the Tate module: induced ℤₚ-linear map
-- statement:
--   Let $p$ be a prime and let $M$, $M'$ be additive commutative groups, and let $\varphi : M \to M'$ be an additive homomorphism. Here, for an additive commutative group $M$, [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) is the additive subgroup of the group $\mathbb{N} \to M$ of all sequences consisting of those $x$ such that for every $n$ one has $(p^n) \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ (integer scalar multiplications), equipped with its $\mathbb{Z}_p$-module structure, in which the action of $a \in \mathbb{Z}_p$ is given levelwise by $(a \cdot x)_n = (a.\mathrm{appr}\,n) \cdot x_n$, the integer approximation of $a$ modulo $p^n$ acting on $x_n$. The assertion is that there exists a $\mathbb{Z}_p$-linear map $T :$ [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) $\to$ [`TateModule p M'`](def/EllipticCurve_TateModule.html#L15) such that for every $x$ in [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) and every $n \in \mathbb{N}$, the $n$-th term of the sequence underlying $T x$ equals $\varphi$ applied to the $n$-th term of the sequence underlying $x$. Only existence is asserted; the uniqueness of such a $T$, immediate from the displayed levelwise formula, is not part of the statement.
--
--   This is the functoriality of the Tate module construction $M \mapsto T_p M = \varprojlim M[p^n]$ in the concrete levelwise form used throughout the project: an additive map of groups induces a $\mathbb{Z}_p$-linear map of Tate modules acting termwise. It is used wherever an endomorphism or homomorphism of an abelian group must be transported to its Tate module, for instance in producing the $\mathbb{Z}_p$-linear map on Tate modules attached to the point-pushforward maps of fake elliptic curves in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_exists_linearMap_forall_apply_eq.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.exists_linearMap_forall_apply_eq
    (p : ℕ) [Fact p.Prime] (M M' : Type) [AddCommGroup M] [AddCommGroup M'] (φ : M →+ M') :
    ∃ T : TateModule p M →ₗ[ℤ_[p]] TateModule p M',
      ∀ (x : TateModule p M) (n : ℕ), ((T x : TateModule p M') : ℕ → M') n = φ ((x : ℕ → M) n) := by sorry
