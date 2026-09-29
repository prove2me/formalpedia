-- Prove2me | Theorems.Thm_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
-- name    : ValuationSubring.exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/688f68f6-c984-587e-97db-963929312f3e
-- title:
--   Inertia at a place over v moves a p₀-th root
-- statement:
--   Let $L'$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ (a fixed algebraic closure of $\mathbb{Q}$) which is a number field, let $p_0$ and $q$ be prime numbers, let $x$ be a unit of $L'$ (that is, a nonzero element), and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{L'}$ such that $q$, viewed in $\mathcal{O}_{L'}$, lies in the prime ideal $v$. Assume that the integer obtained by reading additively the value $v.\mathrm{valuationOfNeZero}\,x \in \mathrm{Multiplicative}\,\mathbb{Z}$ (the exponent of $v$ in $x$, up to the sign convention) is not divisible by $p_0$. Let $y \in \overline{\mathbb{Q}}$ satisfy $y^{p_0} = x$. Then there is a valuation subring $P$ of $\overline{\mathbb{Q}}$ such that: $q$, as an element of $\overline{\mathbb{Q}}$, is a nonunit of $P$; $P$ induces $v$ on $L'$, in the sense that for every $z \in \mathcal{O}_{L'}$ one has $z \in v$ if and only if the $P$-valuation of the image of $z$ in $\overline{\mathbb{Q}}$ is $< 1$; and there is an automorphism $\sigma$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ lying in the image of the inertia subgroup of $P$ inside the decomposition subgroup of $P$, with $\sigma z = z$ for all $z \in L'$ and $\sigma y \neq y$.
--
--   This is the Kummer-theoretic ramification input used in the level-lowering part of the argument: at a place of $\overline{\mathbb{Q}}$ above $q$ restricting to a prescribed prime $v$ of $L'$ at which the valuation of $x$ is prime to $p_0$, the extension $L'(x^{1/p_0})/L'$ is ramified, witnessed by an inertia element fixing $L'$ pointwise and moving the chosen $p_0$-th root. It is cited by [`NumberField.LevelArith.exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation`](thm.html#NumberField.LevelArith.exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation), and differs from the version without the second conjunct precisely by locating $P$ over $v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.lean

import Definitions.Def_FLTPrelim_Ramification
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain

theorem ValuationSubring.exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L']
    (p₀ : ℕ) (hp₀ : p₀.Prime) (x : (L' : Type)ˣ) (v : HeightOneSpectrum (𝓞 L'))
    (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L') ∈ v.asIdeal)
    (hv : ¬ ((p₀ : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)))
    (y : AlgebraicClosure ℚ) (hy : y ^ p₀ = ((x : L') : AlgebraicClosure ℚ)) :
    ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q ∧
      (∀ z : 𝓞 L', z ∈ v.asIdeal ↔ P.valuation (algebraMap L' (AlgebraicClosure ℚ) z) < 1) ∧
      ∃ σ ∈ P.inertiaSubgroupIn ℚ, (∀ z : L', σ z = z) ∧ σ y ≠ y := by sorry
