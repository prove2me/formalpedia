-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic
-- name    : WeierstrassCurve.exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/a7c50476-2a8f-58ac-886d-770ae0a816b4
-- title:
--   Supersingular curve with level structure and odd-degree s-power endomorphism
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, let $M$ be a nonzero natural number and $s$ a prime with $s \neq p$, and assume $p \nmid M$ and $s \nmid M$. Then there exist a Weierstrass curve $E$ over $K$ which is elliptic, an additive subgroup $C$ of the group $E(K)$ of affine points of $E$, additive group endomorphisms $\alpha, \alpha'$ of the affine points of the base change of $E$ to $K$, and a natural number $n$, such that: $E(K)$ has no nonzero $p$-torsion, i.e. $p \cdot P = 0$ forces $P = 0$; $C$ is cyclic with $\#C = M$; $\alpha$ maps every element of $C$ back into $C$; both $\alpha$ and $\alpha'$ lie in [`WeierstrassCurve.rationalHomSet K E E`](def/WeierstrassCurve_RationalEnd.html#L28), meaning each is either the zero map or admits a rational representation — there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $K$ and a finite set $B \subseteq K$ such that for every nonsingular point $(x,y)$ with $x \notin B$ the denominators $d_X, d_Y$ do not vanish at $(x,y)$ and the map sends $(x,y)$ to $(n_X/d_X, n_Y/d_Y)$ evaluated there; $\alpha' \circ \alpha = \alpha \circ \alpha' = s^n \cdot \mathrm{id}$; $n$ is odd; and $\#\ker \alpha = s^n$.
--
--   This produces a supersingular point of $X_0(M)$ in characteristic $p$ carrying a separable endomorphism of degree $s^n$ with $n$ odd that preserves the cyclic level-$M$ structure, the arithmetic input (via complex multiplication and quaternionic orders) for the non-bipartiteness of the $s$-isogeny graph on supersingular points of $X_0(M)$. It is used by [`ModularCurve.SSLevelDatum.exists_fst_mem_iff_snd_mem_of_nonempty`](thm.html#ModularCurve.SSLevelDatum.exists_fst_mem_iff_snd_mem_of_nonempty) in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_supersingular_endomorphism_natCard_ker_eq_odd_pow_stabilizing_cyclic
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M s : ℕ) [NeZero M] (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M) :
    ∃ (E : WeierstrassCurve K) (_ : E.IsElliptic) (C : AddSubgroup E.toAffine.Point)
      (α α' : (E.baseChange K).toAffine.Point →+ (E.baseChange K).toAffine.Point) (n : ℕ),
      (∀ P : E.toAffine.Point, p • P = 0 → P = 0) ∧
      IsAddCyclic C ∧ Nat.card C = M ∧ (∀ T ∈ C, α T ∈ C) ∧
      α ∈ WeierstrassCurve.rationalHomSet K E E ∧ α' ∈ WeierstrassCurve.rationalHomSet K E E ∧
      α'.comp α = s ^ n • AddMonoidHom.id _ ∧ α.comp α' = s ^ n • AddMonoidHom.id _ ∧
      Odd n ∧ Nat.card α.ker = s ^ n := by sorry
