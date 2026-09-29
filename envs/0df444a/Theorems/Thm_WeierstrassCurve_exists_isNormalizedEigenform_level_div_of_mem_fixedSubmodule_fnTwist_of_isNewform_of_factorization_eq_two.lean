-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isNormalizedEigenform_level_div_of_mem_fixedSubmodule_fnTwist_of_isNewform_of_factorization_eq_two
-- name    : WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_mem_fixedSubmodule_fnTwist_of_isNewform_of_factorization_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/e6d35b15-91bd-5de1-a1b0-177f4f61ae17
-- title:
--   Level reduction to L/q for a twisted newform with q² ‖ L
-- statement:
--   Let $p \neq 2$ be a prime, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ which is a semistable model (every prime dividing $\Delta_W$ fails to divide $c_4$) and whose mod $p$ representation is irreducible, in the sense that the $p$-torsion of $W_{\mathbb{Q}}$ over $\overline{\mathbb{Q}}$ is nontrivial and has no Galois-stable $\mathbb{Z}/p$-submodule other than $0$ and itself. Let $M \neq 0$, let $L \mid M$, let $q \neq p$ be a prime with $\operatorname{ord}_q(L) = 2$, let $g$ be a weight-two cusp form for $\Gamma_0(L)$ which is a newform (a normalised eigenform whose system of $\ell$-th coefficients for $\ell \nmid L$ is not matched by a normalised eigenform of any proper divisor level), and let $\mathfrak{m}$ be a maximal ideal of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$ such that for every prime $\ell \neq p$ with $\ell \nmid \Delta_W$ and $\ell \nmid M$ the coefficient $a_\ell(g)$ is an algebraic integer congruent modulo $\mathfrak{m}$ to $\ell + 1 - \#W(\mathbb{F}_\ell)$. Let $\Phi$ be a complex function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ which is an adelic lift of $g$ (left invariant under $\mathrm{GL}_2(\mathbb{Q})$, right invariant under the finite level-one subgroup of level $L$, and agreeing at $i$ with the weight-two slash of $g$ by the archimedean component), and let $\eta$ be an idele class character of $\mathbb{Q}$ which is continuous of finite order, admits the modulus $q\mathcal{O}_{\mathbb{Q}}$, and whose value on the idele equal to $u$ at $q$ and $1$ elsewhere has $p$-power order for every $u \in \mathbb{Z}_q^\times$. Let $y$ be an element of the span of adelic right translates of the twist $(\eta \circ \det) \cdot \Phi$ which lies in the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of the distinguished vector, is nonzero, is fixed by the subgroup $K_1(q)$ of elements of $\mathrm{GL}_2(\mathbb{Z}_q)$ with lower row congruent to $(0,1)$ modulo $q$, and on which the central element $\mathrm{diag}(u,u)$, $u \in \mathbb{Z}_q^\times$, acts by the square of the corresponding value of $\eta$. Then there exist a cusp form $f$ of weight two for $\Gamma_0(L/q)$ and a maximal ideal $\mathfrak{m}'$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ such that $f$ is a normalised eigenform, $p \in \mathfrak{m}'$, and for every prime $\ell \neq p$ with $\ell \nmid \Delta_W$ and $\ell \nmid M$ the coefficient $a_\ell(f)$ is an algebraic integer congruent to $\ell + 1 - \#W(\mathbb{F}_\ell)$ modulo $\mathfrak{m}'$.
--
--   This is the nebentypus-switching step in the level-lowering chain: from a newform of level $L$ with $q^2 \| L$, congruent to the Frey curve away from $M$, together with a twist of its adelic lift by a finite-order character ramified only at $q$ and a vector with $K_1(q)$-invariance and prescribed central character, one produces a normalised eigenform of level $L/q$ satisfying the same residual congruences at good primes. It feeds the corresponding statement at level $L/q$ from which the hypotheses on $\Phi$, $\eta$ and $y$ have been eliminated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isNormalizedEigenform_level_div_of_mem_fixedSubmodule_fnTwist_of_isNewform_of_factorization_eq_two.lean

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.NumberTheory.Padics.RingHoms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_mem_fixedSubmodule_fnTwist_of_isNewform_of_factorization_eq_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p) {M : ℕ} [NeZero M] {L : ℕ}
    (hLM : L ∣ M) {q : ℕ} (hqp : q ≠ p) (hq2 : L.factorization q = 2)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (𝔪 : Ideal (integralClosure ℤ ℂ))
    (hg : g.IsNewform) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪)
    [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (hηmod : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel q))
    (hηp : ∀ u : ℤ_[q]ˣ, ∃ n : ℕ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
        (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) ^ p ^ n = 1)
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hy0 : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q 1)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y =
      ((η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
              (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2) • y) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 (L / q)) 2) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      f.IsNormalizedEigenform ∧ 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪' := by sorry
