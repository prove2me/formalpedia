-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isNormalizedEigenform_level_div_of_isNewform_of_factorization_eq_two
-- name    : WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_isNewform_of_factorization_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/4c65dc25-f364-5fa6-879e-008b48789525
-- title:
--   Lowering the q-exponent from two to one in the level
-- statement:
--   Let $p$ be an odd prime, and let $W$ be a Weierstrass equation over $\mathbb{Z}$ with $\Delta \neq 0$ which is a semistable model, i.e. no prime dividing $\Delta$ divides $c_4$, and whose mod-$p$ representation is irreducible in the sense that the $p$-torsion of the group of points of $W$ over an algebraic closure of $\mathbb{Q}$ is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $\bot$ and $\top$. Let $M$ be a nonzero natural number, $L \mid M$, and let $q \neq p$ occur in the factorisation of $L$ with exponent exactly $2$ (so $q$ is prime). Let $g$ be a weight-two cusp form for $\Gamma_0(L)$ which is a newform, i.e. a normalised eigenform (first $q$-coefficient $1$, multiplicativity on coprime indices, and the two Hecke recursions at prime powers according as the prime divides $L$ or not) whose system of coefficients at primes not dividing $L$ is matched by no normalised eigenform of any proper divisor level, and let $\mathfrak{m}$ be a maximal ideal of the ring of algebraic integers $\overline{\mathbb{Z}} \subset \mathbb{C}$ containing $p$ such that for every prime $\ell \neq p$ with $\ell \nmid \Delta$ and $\ell \nmid M$ the $\ell$-th coefficient of $g$ lies in $\overline{\mathbb{Z}}$ and is congruent modulo $\mathfrak{m}$ to $a_\ell(W) = \ell + 1 - \#W(\mathbb{Z}/\ell)$. Then there are a weight-two cusp form $f$ for $\Gamma_0(L/q)$ which is a normalised eigenform and a maximal ideal $\mathfrak{m}'$ of $\overline{\mathbb{Z}}$ containing $p$ satisfying the same congruence: for every prime $\ell \neq p$ with $\ell \nmid \Delta$ and $\ell \nmid M$, the $\ell$-th coefficient of $f$ is an algebraic integer congruent to $a_\ell(W)$ modulo $\mathfrak{m}'$. Only a normalised eigenform, not a newform, is produced at the smaller level.
--
--   This is the level-lowering step that removes one factor of a prime $q \neq p$ occurring to exponent exactly two in the level, in the form needed for the Frey curve: the mod-$p$ eigensystem attached to $W$ is realised at level $L/q$. It feeds the reduction of the level to its squarefree part in [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_prime_sq_dvd_of_not_cube_dvd`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_prime_sq_dvd_of_not_cube_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isNormalizedEigenform_level_div_of_isNewform_of_factorization_eq_two.lean

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_Newforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_isNewform_of_factorization_eq_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p) {M : ℕ} [NeZero M] {L : ℕ}
    (hLM : L ∣ M) {q : ℕ} (hqp : q ≠ p) (hq2 : L.factorization q = 2)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (𝔪 : Ideal (integralClosure ℤ ℂ))
    (hg : g.IsNewform) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 (L / q)) 2) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      f.IsNormalizedEigenform ∧ 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪' := by sorry
