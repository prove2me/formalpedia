-- Prove2me | Theorems.Thm_RatIdele_sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one
-- name    : RatIdele.sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/3063371c-2f9e-5598-9222-156f32dbc270
-- title:
--   Everywhere-unit finite idele congruent to its residue mod M
-- statement:
--   Fix a natural number $M \neq 0$ and a unit $u$ of the finite adele ring $\mathbb{A}_{\mathbb{Q},f}$ of $\mathbb{Q}$ (formed from $\mathcal{O}_{\mathbb{Q}} = \mathbb{Z}$ and $\mathbb{Q}$), and assume that $u$ is a unit at every finite place: for every $v$ in the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ the valuation of the $v$-component of $u$ equals $1$. Let $x = (1, u)$ be the image of $u$ under [`NumberField.AdelicLevel.finIncl`](def/NumberField_AdelicLevel.html#L636), the monoid embedding of the finite adeles into the full adele ring sending $y \mapsto (1, y)$, applied to units, and let $r = \mathrm{unitResidue}\,M\,(x) \in \mathbb{Z}/M$ be the element obtained, via the inverse of the Chinese remainder isomorphism $\mathbb{Z}/M \simeq \prod_{p \mid M} \mathbb{Z}/p^{\mathrm{ord}_p M}$, from the family of reductions `PadicInt.toZModPow (M.factorization p)` of the $p$-adic unit components [`RatIdele.unitPadicAt p x`](def/DirichletCharacter_DirichletIdeleChar.html#L19), for $p$ running over the prime factors of $M$. The assertion is that $u - r.\mathrm{val}$, where $r.\mathrm{val} \in \{0,\dots,M-1\}$ is the canonical representative cast into the finite adeles, lies in the ideal ball of $(M) =$ `Ideal.span {(M : 𝓞 ℚ)}`, that is, at every finite place $v$ the valuation of the $v$-component of $u - r.\mathrm{val}$ is at most $\exp(-\mathrm{ord}_v(M))$; equivalently $u_v \equiv r.\mathrm{val} \pmod{M\mathcal{O}_v}$ for all $v$.
--
--   This is the compatibility between the adelic residue homomorphism $\mathbb{A}_{\mathbb{Q}}^\times \to \mathbb{Z}/M$ used to define Dirichlet characters adelically and congruences in the completed local rings: an everywhere-unit finite idele is congruent modulo $M$, at every finite place simultaneously, to a single rational integer representing its residue. It is used in the identification of the nebentypus of an adelic lift of a modular form of level $\Gamma_1(M)$ with a finite-order Hecke character times a central scalar.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RatIdele_sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one.lean

import Definitions.Def_DirichletCharacter_DirichletIdeleChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem RatIdele.sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one
    (M : ℕ) [NeZero M] (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1) :
    (u : FiniteAdeleRing (𝓞 ℚ) ℚ)
        - ((RatIdele.unitResidue M (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) u)).val : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ NumberField.AdelicLevel.idealBall (𝓞 ℚ) ℚ (Ideal.span {((M : ℕ) : 𝓞 ℚ)}) := by sorry
