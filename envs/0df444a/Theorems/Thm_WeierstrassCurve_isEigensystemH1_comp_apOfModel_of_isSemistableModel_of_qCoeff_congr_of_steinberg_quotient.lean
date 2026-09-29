-- Prove2me | Theorems.Thm_WeierstrassCurve_isEigensystemH1_comp_apOfModel_of_isSemistableModel_of_qCoeff_congr_of_steinberg_quotient
-- name    : WeierstrassCurve.isEigensystemH1_comp_apOfModel_of_isSemistableModel_of_qCoeff_congr_of_steinberg_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/2d0e90fc-3662-58eb-8660-4a94a40cddd6
-- title:
--   Level lowering at q² with Steinberg-quotient coefficients
-- statement:
--   Let $p$ be a prime with $p \neq 2$ and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta \neq 0$ which is a semistable model, i.e. no prime dividing $\Delta$ divides $c_4$, and whose mod $p$ representation is irreducible in the sense that the $p$-torsion of $W$ over an algebraic closure of $\mathbb{Q}$ is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $0$ and the whole module. Let $M \neq 0$, let $L \mid M$, and let $q$ be a prime with $q \neq p$ and $\operatorname{ord}_q(L) = 2$, with $L/q^2 \neq 0$. Let $g$ be a weight $2$ cusp form on $\Gamma_0(L)$ which is a newform, that is, a normalised eigenform whose eigensystem away from $L$ is not matched by a normalised eigenform of any proper divisor level, and let $\mathfrak{m}$ be a maximal ideal of the ring of algebraic integers $\operatorname{integralClosure} \mathbb{Z}\,\mathbb{C}$ containing $p$, such that for every prime $\ell$ with $\ell \nmid \Delta$, $\ell \nmid M$ and $\ell \neq p$ the $\ell$-th $q$-expansion coefficient of $g$ is the image of an algebraic integer $a$ with $a - a_\ell(W) \in \mathfrak{m}$, where $a_\ell(W) = \ell + 1 - \#W(\mathbb{Z}/\ell)$ is the trace of Frobenius of the reduction of $W$ modulo $\ell$. Assume $q \equiv -1 \pmod p$, and assume that $g$ has no principal-series component at $q$ in the following form: for every nonzero function $\Phi$ on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ which is an adelic lift of $g$, every pair of characters $\mu_1, \mu_2 : \mathbb{Q}_q^{\times} \to \mathbb{C}^{\times}$ and every $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant $\mathbb{C}$-linear map from the adelic span of $\Phi$ to the principal series attached to $(\mu_1,\mu_2)$ vanishes. Finally let $\kappa$ be a field of characteristic $p$, let $\rho$ be a representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on a finite-dimensional $\kappa$-vector space $V$, and let $\pi$ be a $\kappa$-linear map from the Steinberg submodule, the kernel of the coefficient-sum map on $\kappa$-valued finitely supported functions on $\mathbb{P}^1(\mathbb{Z}/q)$, to $V$ which intertwines the natural $\mathrm{GL}_2(\mathbb{Z}/q)$-action with $\rho$, is surjective, and whose kernel consists exactly of the scalar multiples of the constant function $1$. Then the predicate [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) holds at level $L/q^2$ for the representation of $\Gamma_0(L/q^2)$ obtained by reducing matrices modulo $q$, passing from $\mathrm{SL}_2$ to $\mathrm{GL}_2$ and applying $\rho$, with coefficient operators $\ell \mapsto \rho(\mathrm{diag}(\ell,1))$ when $\ell \not\equiv 0 \pmod q$ and the identity otherwise, with excluded set $\{\ell \mid \ell \mid \Delta \text{ or } \ell \mid M \text{ or } \ell = p\}$, and with eigenvalue system $\ell \mapsto$ the image of $a_\ell(W)$ in $\kappa$: there is a nonzero class $x$ in the coefficient cohomology $H^1$ of that representation such that for every prime $\ell$ not dividing $L/q^2$ and outside the excluded set there is an endomorphism $T$ of $H^1$ which is a Hecke operator at $\ell$ for the given coefficient operator and satisfies $T x = a_\ell(W) \cdot x$.
--
--   This is the level-lowering step that removes the square factor $q^2$ from the level, in the form of an occurrence of the mod $p$ eigensystem of $W$ in the $\Gamma_0(L/q^2)$-cohomology with coefficients in a Steinberg quotient at $q$. It feeds the statement [`WeierstrassCurve.exists_charP_rep_steinberg_quotient_isEigensystemH1_apOfModel_of_isSemistableModel_of_qCoeff_congr`](thm.html#WeierstrassCurve.exists_charP_rep_steinberg_quotient_isEigensystemH1_apOfModel_of_isSemistableModel_of_qCoeff_congr), where the coefficient field and Steinberg quotient are produced rather than assumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isEigensystemH1_comp_apOfModel_of_isSemistableModel_of_qCoeff_congr_of_steinberg_quotient.lean

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem
WeierstrassCurve.isEigensystemH1_comp_apOfModel_of_isSemistableModel_of_qCoeff_congr_of_steinberg_quotient
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
    [NeZero (L / q ^ 2)]
    (κ : Type) [Field κ] [CharP κ p]
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ) :
      HeckeEis.IsEigensystemH1 (L / q ^ 2) (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 (L / q ^ 2)).subtype))
        (fun ℓ : ℕ =>
          if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
        {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ = p} (fun ℓ => ((W.apOfModel ℓ : ℤ) : κ)) := by sorry
