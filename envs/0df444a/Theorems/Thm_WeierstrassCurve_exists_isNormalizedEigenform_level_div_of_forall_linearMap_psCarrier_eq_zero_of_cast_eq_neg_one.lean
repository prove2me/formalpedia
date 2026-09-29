-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isNormalizedEigenform_level_div_of_forall_linearMap_psCarrier_eq_zero_of_cast_eq_neg_one
-- name    : WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_forall_linearMap_psCarrier_eq_zero_of_cast_eq_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/7e88212a-11cf-5540-8705-2aec601ee23f
-- title:
--   Level lowering at q with q² ∥ L, q≡-1, supercuspidal case
-- statement:
--   Let $p$ be a prime with $p\neq 2$, and let $W$ be a Weierstrass equation over $\mathbb{Z}$ with $\Delta_W\neq 0$ which is a semistable model, i.e. for every prime $\ell$ dividing $\Delta_W$ one has $\ell\nmid c_4(W)$, and whose mod-$p$ representation is irreducible in the sense that the $p$-torsion of the points of $W_{\mathbb{Q}}$ over $\overline{\mathbb{Q}}$ is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $0$ and the whole module. Let $M$ be a nonzero natural number, $L\mid M$, and $q\neq p$ a prime with $\mathrm{ord}_q(L)=2$. Let $g$ be a weight-two cusp form for $\Gamma_0(L)$ that is a newform, i.e. a normalised eigenform (first $q$-coefficient $1$, coefficients multiplicative at coprime arguments, and the usual recursions at prime powers according as the prime divides $L$ or not) for which no proper divisor $N\mid L$, $N\neq L$, carries a normalised eigenform with the same $\ell$-th coefficients for all primes $\ell\nmid L$. Let $\mathfrak{m}$ be a maximal ideal of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ with $p\in\mathfrak{m}$, and assume that for every prime $\ell\neq p$ with $\ell\nmid\Delta_W$ and $\ell\nmid M$ the $\ell$-th $q$-expansion coefficient of $g$ is the image of some $a$ in that integral closure with $a\equiv a_\ell(W)\pmod{\mathfrak{m}}$, where $a_\ell(W)$ is the trace of Frobenius of the reduction of $W$ mod $\ell$. Assume $q\equiv-1\pmod p$, and that the local component of $g$ at $q$ admits no principal-series quotient: for every nonzero $\Phi$ on the adelic $\mathrm{GL}_2$ of $\mathbb{Q}$ which is an adelic lift of $g$ (left invariant under the global points, right invariant under the level-one subgroup at the finite level attached to $L$, and matching the weight-two slash action of $g$ at $\mathrm{i}$ on the archimedean part), for all characters $\mu_1,\mu_2:\mathbb{Q}_q^\times\to\mathbb{C}^\times$, every $\mathbb{C}$-linear $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant map from the adelic span of $\Phi$ to the principal-series carrier attached to $(\mu_1,\mu_2)$ vanishes. Then there exist a weight-two cusp form $f$ for $\Gamma_0(L/q)$ which is a normalised eigenform and a maximal ideal $\mathfrak{m}'$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$ such that for every prime $\ell\neq p$ with $\ell\nmid\Delta_W$ and $\ell\nmid M$ the $\ell$-th coefficient of $f$ is an algebraic integer congruent to $a_\ell(W)$ modulo $\mathfrak{m}'$.
--
--   This is the level-lowering step that removes a prime $q$ occurring to exponent exactly $2$ in the level, under the hypotheses $q\equiv-1\pmod p$ and that the local representation at $q$ is not a subquotient of a principal series; the congruence with the semistable curve $W$ is transported from level $L$ to level $L/q$. It feeds the deduction that the mod-$p$ eigensystem of $W$ occurs at a level divisible only by the remaining primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isNormalizedEigenform_level_div_of_forall_linearMap_psCarrier_eq_zero_of_cast_eq_neg_one.lean

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_forall_linearMap_psCarrier_eq_zero_of_cast_eq_neg_one
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p) {M : ℕ} [NeZero M] {L : ℕ}
    (hLM : L ∣ M) {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (hq2 : L.factorization q = 2)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (𝔪 : Ideal (integralClosure ℤ ℂ))
    (hg : g.IsNewform) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪)
    (hq1 : ((q : ℕ) : ZMod p) = -1)
    (hps : ∀ (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ),
      Φ ≠ 0 → g.IsAdelicLiftOf Φ →
      ∀ (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
        (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂),
        (∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) → f = 0) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 (L / q)) 2) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      f.IsNormalizedEigenform ∧ 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪' := by sorry
