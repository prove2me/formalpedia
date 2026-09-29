-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isNewform_of_inertia_moves_torsion_of_two_dvd_of_eq_three
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_div_of_isNewform_of_inertia_moves_torsion_of_two_dvd_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/a0ad5674-b3b0-5902-ab60-ed764dd86875
-- title:
--   Level descent at p=3 from a newform of level divisible by 9
-- statement:
--   Let $p$ be a prime with $p \neq 2$ and $p = 3$, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta(W) \neq 0$ which is a semistable model in the sense that for every prime $q$ dividing $\Delta(W)$ one has $q \nmid c_4(W)$, and whose mod $p$ representation is irreducible, i.e. the $p$-torsion of the base change of $W$ to $\mathbb{Q}$, taken over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $\bot$ and $\top$. Let $M \geq 1$ be such that $p^2 \mid M$ implies $2 \mid M$, and such that, if $p^2 \mid M$, then for every valuation subring $A$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with $p$ a nonunit of $A$, every $p$-torsion point fixed by all elements of the inertia subgroup of $A$ over $\mathbb{Q}$ (the image in $\mathrm{Gal}$ of the inertia subgroup inside the decomposition subgroup) is zero. Let $L \mid M$ with $p^2 \mid L$, let $g$ be a weight $2$ cusp form on $\Gamma_0(L)$ and $\mathfrak{m}$ a maximal ideal of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, with $g$ a newform: $g$ is a normalised eigenform (first $q$-coefficient $1$, multiplicativity at coprime arguments, and the usual prime-power recursions according as the prime divides $L$ or not) and no proper divisor of $L$ carries a normalised eigenform whose $q$-coefficients at primes not dividing $L$ agree with those of $g$. Assume finally that for every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid M$ and $\ell \neq p$ there is an algebraic integer $a$ equal to the $\ell$-th $q$-coefficient of $g$ with $a - a_\ell(W) \in \mathfrak{m}$, where $a_\ell(W) = \ell + 1 - \#(W \bmod \ell)$. The conclusion is that $W$ is residually modular of level $M/p$: there exist a weight $2$ cusp form $f$ on $\Gamma_0(M/p)$ which is a normalised eigenform, and a maximal ideal $\mathfrak{m}'$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, such that for every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid M/p$ and $\ell \neq p$ there is an algebraic integer $a$ equal to the $\ell$-th $q$-coefficient of $f$ with $a - a_\ell(W) \in \mathfrak{m}'$.
--
--   This is the $p = 3$ instance of the conditional level-lowering step at $p$ in the Frey-curve argument: from a newform witness at a level divisible by $p^2$ whose Hecke eigenvalues are congruent mod a maximal ideal above $p$ to the traces of Frobenius of $W$, one obtains such a witness at level $M/p$. It asserts no modularity of $W$ on its own, everything being conditional on the bound newform $g$; it feeds the removal of the full $p$-part of the level in [`WeierstrassCurve.isResiduallyModularOfLevel_mul_ordCompl_of_inertia_moves_torsion_of_two_dvd_of_eq_three`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_mul_ordCompl_of_inertia_moves_torsion_of_two_dvd_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isNewform_of_inertia_moves_torsion_of_two_dvd_of_eq_three.lean

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.isResiduallyModularOfLevel_div_of_isNewform_of_inertia_moves_torsion_of_two_dvd_of_eq_three
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p = 3) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p) {M : ℕ} [NeZero M]
    (h2M : p ^ 2 ∣ M → 2 ∣ M)
    (hns : p ^ 2 ∣ M →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) → x = 0)
    {L : ℕ}
    (hLM : L ∣ M) (hpL : p ^ 2 ∣ L)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (𝔪 : Ideal (integralClosure ℤ ℂ))
    (hg : g.IsNewform) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) :
    W.IsResiduallyModularOfLevel p (M / p) := by sorry
