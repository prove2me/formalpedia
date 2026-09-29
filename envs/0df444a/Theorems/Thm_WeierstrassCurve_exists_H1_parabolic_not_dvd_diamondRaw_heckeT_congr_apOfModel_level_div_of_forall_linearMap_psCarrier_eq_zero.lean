-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_H1_parabolic_not_dvd_diamondRaw_heckeT_congr_apOfModel_level_div_of_forall_linearMap_psCarrier_eq_zero
-- name    : WeierstrassCurve.exists_H1_parabolic_not_dvd_diamondRaw_heckeT_congr_apOfModel_level_div_of_forall_linearMap_psCarrier_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/3fec21b6-3450-552f-8673-55ce6be373b3
-- title:
--   Integral mod-p parabolic eigenclass at level L/q
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ which is a semistable model in the sense that $\ell \mid \Delta_W$ implies $\ell \nmid c_4(W)$ for every prime $\ell$, and whose mod-$p$ representation is irreducible (`ModRepIsIrreducible`, i.e. the Galois representation on the $p$-torsion of $W$ over $\mathbb{Q}$, taken in $\overline{\mathbb{Q}}$, is irreducible). Let $M \neq 0$, let $L \mid M$, let $q \neq p$ be a prime with $q$-adic valuation of $L$ exactly $2$, let $g$ be a weight-two cusp form on $\Gamma_0(L)$ which is a newform (a normalised eigenform whose good eigensystem occurs at no proper divisor of $L$), and let $\mathfrak{m}$ be a maximal ideal of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$. Assume: for every prime $\ell$ with $\ell \nmid \Delta_W$, $\ell \nmid M$ and $\ell \neq p$ there is an algebraic integer $a$ with $a = a_\ell(g)$, the $\ell$-th $q$-expansion coefficient of $g$, and $a - a_\ell(W) \in \mathfrak{m}$, where $a_\ell(W)$ is the trace of Frobenius of the reduction of $W$ mod $\ell$; $q \equiv -1 \pmod p$; and the local cuspidality hypothesis that for every non-zero function $\Phi$ on the adelic $\mathrm{GL}_2$ of $\mathbb{Q}$ of which $g$ is an adelic lift (left invariance under the global points, right invariance under the finite level-one subgroup attached to level $L$, and the prescribed archimedean slash formula at $\mathrm{i}$), for all characters $\mu_1, \mu_2$ of $\mathbb{Q}_q^{\times}$, every $\mathbb{C}$-linear $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant map from the adelic span of $\Phi$ to the principal-series carrier [`LocalNewvector.PSCarrier q μ₁ μ₂`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173) vanishes. Assume finally $L/q \neq 0$. Then there exists $\varphi_0$ in [`CohCarrier.H1 (L / q) ⊥ ℤ`](def/CohCarrier_Level.html#L162), the group of additive homomorphisms from the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ cut out inside $\Gamma_0(L/q)$ by the trivial subgroup of $(\mathbb{Z}/(L/q))^{\times}$ to $\mathbb{Z}$, such that: $\varphi_0$ lies in [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62), the submodule of homomorphisms vanishing on the elements singled out by `IsParabolicHom`; $\varphi_0$ is not $p$ times any class; for every $\sigma \in \Gamma_0(L/q)$ the difference `diamondRaw` $(\sigma)\varphi_0 - \varphi_0$ is divisible by $p$; and for every prime $\ell$ with $\ell \nmid \Delta_W$, $\ell \nmid M$ and $\ell \neq p$ the difference $T_\ell \varphi_0 - a_\ell(W)\varphi_0$ is divisible by $p$, with $T_\ell$ the operator [`CohCarrier.heckeT`](def/CohCarrier_Level.html#L250) at level $L/q$.
--
--   This is the cohomological level-lowering step that removes one power of $q$ from the level when the local component of the newform at $q$ is not a principal series: from a mod-$\mathfrak{m}$ congruence between the form $g$ of level $L$ with $q^2 \parallel L$ and the curve $W$, it produces an integral parabolic class of level $L/q$, primitive mod $p$, on which the diamond operators act trivially and the Hecke operators act by the Frobenius traces of $W$, all modulo $p$. It feeds the reconstruction of a normalised eigenform of level $L/q$ in [`WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_forall_linearMap_psCarrier_eq_zero_of_cast_eq_neg_one`](thm.html#WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_forall_linearMap_psCarrier_eq_zero_of_cast_eq_neg_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_H1_parabolic_not_dvd_diamondRaw_heckeT_congr_apOfModel_level_div_of_forall_linearMap_psCarrier_eq_zero.lean

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_H1_parabolic_not_dvd_diamondRaw_heckeT_congr_apOfModel_level_div_of_forall_linearMap_psCarrier_eq_zero
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
        (∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) → f = 0)
    [NeZero (L / q)] :
    ∃ φ₀ : CohCarrier.H1 (L / q) ⊥ ℤ,
      φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH (L / q) ⊥) ℤ ∧
      (¬ ∃ ψ : CohCarrier.H1 (L / q) ⊥ ℤ, φ₀ = (p : ℤ) • ψ) ∧
      (∀ σ : CongruenceSubgroup.Gamma0 (L / q), ∃ ψ : CohCarrier.H1 (L / q) ⊥ ℤ,
        CohCarrier.diamondRaw (L / q) ⊥ ℤ σ φ₀ - φ₀ = (p : ℤ) • ψ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ ψ : CohCarrier.H1 (L / q) ⊥ ℤ, CohCarrier.heckeT (L / q) ⊥ ℓ ℤ φ₀ - (W.apOfModel ℓ) • φ₀ = (p : ℤ) • ψ) := by sorry
