-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_charP_rep_steinberg_quotient_isEigensystemH1_apOfModel_of_isSemistableModel_of_qCoeff_congr
-- name    : WeierstrassCurve.exists_charP_rep_steinberg_quotient_isEigensystemH1_apOfModel_of_isSemistableModel_of_qCoeff_congr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/30b6732c-bdb7-54cb-8b33-48266a854a0a
-- title:
--   Mod p eigensystem of W on H¹ with Steinberg-quotient coefficients
-- statement:
--   Let $p$ be a prime with $p \neq 2$ and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ which is semistable in the sense that no prime dividing $\Delta_W$ divides $c_4(W)$, and whose mod $p$ representation is irreducible, i.e. the $p$-torsion of $W$ over an algebraic closure of $\mathbb{Q}$ is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $0$ and everything. Let $M \geq 1$, let $L \mid M$, and let $q$ be a prime with $q \neq p$ whose exponent in $L$ is exactly $2$ and with $q \equiv -1 \pmod p$. Let $g$ be a weight $2$ cusp form on $\Gamma_0(L)$ which is a newform (a normalised eigenform whose system of coefficients away from $L$ occurs at no proper divisor of $L$), and let $\mathfrak{m}$ be a maximal ideal of the ring of algebraic integers containing $p$, such that for every prime $\ell \nmid M$ with $\ell \neq p$ and $\ell \nmid \Delta_W$ the coefficient $a_\ell(g)$ is an algebraic integer congruent to $a_\ell(W) = \#\mathbb{F}_\ell + 1 - \#W(\mathbb{F}_\ell)$ modulo $\mathfrak{m}$. Assume further that for every nonzero adelic lift $\Phi$ of $g$ on $\mathrm{GL}_2$ over $\mathbb{Q}$, every $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant $\mathbb{C}$-linear map from the span of the translates of $\Phi$ into a principal series $\mathrm{PSCarrier}$ for characters $\mu_1,\mu_2$ of $\mathbb{Q}_q^\times$ vanishes, and that $L/q^2 \neq 0$. Then there are a field $\kappa$ of characteristic $p$, a finite-dimensional $\kappa$-representation $\rho$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $V$, and a $\kappa$-linear map $\pi$ from the Steinberg submodule (the kernel of the coefficient sum on $\kappa$-valued functions on the projective line over $\mathbb{Z}/q$) to $V$ which is equivariant for the permutation action, surjective, and has kernel exactly the $\kappa$-multiples of the constant function $1$, such that the eigensystem $\ell \mapsto a_\ell(W)$ in $\kappa$ occurs on $H^1$ of $\Gamma_0(L/q^2)$ with coefficients in $V$ via reduction $\Gamma_0(L/q^2) \to \mathrm{SL}_2(\mathbb{Z}/q) \to \mathrm{GL}_2(\mathbb{Z}/q)$: there is a nonzero cohomology class $x$ such that for every prime $\ell$ not dividing $L/q^2$ and outside the set of $\ell$ with $\ell \mid \Delta_W$, $\ell \mid M$ or $\ell = p$, some operator $T$ realising the Hecke correspondence at $\ell$ with coefficient map $\rho(\mathrm{diag}(\ell,1))$ when $\ell \not\equiv 0 \pmod q$ (and the identity otherwise) satisfies $T x = a_\ell(W) \cdot x$.
--
--   This is the level-lowering step at a prime $q$ exactly dividing the level to the second power with $q \equiv -1 \pmod p$: the mod $p$ eigensystem of the semistable curve $W$, realised on a newform of level $L$, is transported to the cohomology of $\Gamma_0(L/q^2)$ with coefficients in the quotient of the Steinberg representation of $\mathrm{GL}_2(\mathbb{F}_q)$ by the constants. It feeds the subsequent extraction of a parabolic cohomology class of level prime to $q$ with the same Hecke eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_charP_rep_steinberg_quotient_isEigensystemH1_apOfModel_of_isSemistableModel_of_qCoeff_congr.lean

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
WeierstrassCurve.exists_charP_rep_steinberg_quotient_isEigensystemH1_apOfModel_of_isSemistableModel_of_qCoeff_congr
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
    [NeZero (L / q ^ 2)] :
    ∃ (κ : Type) (_ : Field κ) (_ : CharP κ p)
      (V : Type) (_ : AddCommGroup V) (_ : Module κ V) (_ : FiniteDimensional κ V)
      (ρ : Representation κ (CuspidalType.GL2 q) V)
      (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V),
      (∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v)) ∧
      Function.Surjective π ∧
      (∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ) ∧
      HeckeEis.IsEigensystemH1 (L / q ^ 2) (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 (L / q ^ 2)).subtype))
        (fun ℓ : ℕ =>
          if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
        {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ = p} (fun ℓ => ((W.apOfModel ℓ : ℤ) : κ)) := by sorry
