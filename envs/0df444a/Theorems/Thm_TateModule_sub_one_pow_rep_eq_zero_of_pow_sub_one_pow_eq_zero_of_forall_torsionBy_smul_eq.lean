-- Prove2me | Theorems.Thm_TateModule_sub_one_pow_rep_eq_zero_of_pow_sub_one_pow_eq_zero_of_forall_torsionBy_smul_eq
-- name    : TateModule.sub_one_pow_rep_eq_zero_of_pow_sub_one_pow_eq_zero_of_forall_torsionBy_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/90550dea-a191-5cb4-8c34-83987eaabfc8
-- title:
--   Rigidity of the Tate module under fixing the pᵃ-torsion
-- statement:
--   Let $p$ be a prime, let $M$ be an additive abelian group, and let $G$ be a monoid acting on $M$ by additive maps. Recall that [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) is the subgroup of sequences $x : \mathbb{N} \to M$ satisfying $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$ (so the inverse limit of the $p^n$-torsion of $M$ along multiplication by $p$), carrying its natural $\mathbb{Z}_p$-module structure, and that [`TateModule.rep p M G`](def/EllipticCurve_TateModule.html#L174) is the monoid homomorphism from $G$ to $\mathrm{End}_{\mathbb{Z}_p}(\mathrm{T}_p M)$ sending $g$ to the endomorphism acting by $g$ in each component. Fix $g \in G$ and a natural number $a$ with $3 \le p^a$, and assume that $g$ fixes every element $x$ of the $\mathbb{Z}$-submodule of $M$ annihilated by $p^a$, i.e. $g \cdot x = x$ whenever $(p^a) \cdot x = 0$. Let $m$ be a positive natural number and $n$ a natural number, and suppose that $\bigl(\rho(g)^m - 1\bigr)^n = 0$ in $\mathrm{End}_{\mathbb{Z}_p}(\mathrm{T}_p M)$, where $\rho =$ [`TateModule.rep p M G`](def/EllipticCurve_TateModule.html#L174). Then $\bigl(\rho(g) - 1\bigr)^n = 0$.
--
--   This is the rigidity statement for the congruence subgroup of level $p^a \ge 3$ acting on a $p$-adic Tate module: an element fixing the $p^a$-torsion and acting quasi-unipotently on $\mathrm{T}_p M$ acts unipotently, and (the case $n = 1$) one acting through a finite quotient acts trivially. It is used in the Čerednik–Drinfeld part of the construction, where inertia elements acting on Tate modules of fake elliptic curves are shown to act trivially or unipotently.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_sub_one_pow_rep_eq_zero_of_pow_sub_one_pow_eq_zero_of_forall_torsionBy_smul_eq.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.sub_one_pow_rep_eq_zero_of_pow_sub_one_pow_eq_zero_of_forall_torsionBy_smul_eq
    {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] {G : Type} [Monoid G] [DistribMulAction G M]
    (g : G) {a : ℕ} (ha : 3 ≤ p ^ a)
    (hfix : ∀ x ∈ Submodule.torsionBy ℤ M ((p ^ a : ℕ) : ℤ), g • x = x)
    {m : ℕ} (hm : 0 < m) {n : ℕ}
    (hn : ((TateModule.rep p M G g) ^ m - 1) ^ n = 0) :
    (TateModule.rep p M G g - 1) ^ n = 0 := by sorry
