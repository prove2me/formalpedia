-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits
-- name    : TwistedUnipotentTerm.semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/5601b541-f855-5062-8620-a36946d5d9f7
-- title:
--   Semi-local character as a product of Hecke-generator powers
-- statement:
--   Let $L/K$ be an extension of number fields, let $\xi_L$ be a homomorphism from the full unit group of the adele ring of $L$ (presented as the top subgroup of $(\mathbb{A}_L)^\times$) to $\mathbb{C}^\times$, and let $v$ be a nonzero prime of $\mathcal{O}_K$. For a unit $\zeta$ of the semi-local algebra $L \otimes_K K_v$ write $\zeta_w$ for its component in $L_w^\times$ under the base-change isomorphism $L \otimes_K K_v \cong \prod_{w} L_w$, the product being over the primes $w$ of $\mathcal{O}_L$ with $w \cap \mathcal{O}_K = v$, and let $\xi_{L,v}(\zeta) = \prod_{w} \xi_L\bigl(\det \mathrm{diag}(\zeta_w,1)\bigr)$ be the semi-local character, the Hecke generator $\mathrm{diag}(\zeta_w,1) \in GL_2(\mathbb{A}_L)$ having entry $\zeta_w$ at $w$ and $1$ at all other places. Assume $\xi_{L,v}(\eta) = 1$ for every $\eta$ in the subgroup of integral units, namely the units of the image submonoid of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_v \to L \otimes_K K_v$. Then for every unit $\zeta$ of $L \otimes_K K_v$ one has $$\xi_{L,v}(\zeta) = \prod_{w} \xi_L\bigl(\det \mathrm{diag}(\varpi_w,1)\bigr)^{-\log |\zeta_w|_w},$$ a finite product over the same index set, where $\varpi_w$ is the chosen uniformiser of $L_w$ and $-\log$ of the $\mathbb{Z}^{m0}$-valued $w$-adic valuation is the normalised additive valuation $\mathrm{ord}_w(\zeta_w)$.
--
--   This is the statement that a character of the idele units which is trivial on the integral units above $v$ is unramified at every place $w \mid v$, so that its semi-local restriction depends only on the orders $\mathrm{ord}_w(\zeta_w)$ and is given by the corresponding powers of its values on the Hecke generators at the places above $v$. It is used in the evaluation of the semi-local unipotent orbital function of a Hecke word above $v$, where it identifies the central contribution as a power of the Hecke-generator values times a counting function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

theorem TwistedUnipotentTerm.semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (hξv : ∀ ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = 1)
    (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ =
      ∏ᶠ w : v.Extension (𝓞 L),
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w.1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          (-WithZero.log (Valued.v
            ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) :
              w.1.adicCompletion L))) := by sorry
