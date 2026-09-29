-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_semiLocalCharacter_congr_eq_of_forall_unitsAct_eq
-- name    : TwistedUnipotentTerm.semiLocalCharacter_congr_eq_of_forall_unitsAct_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ff8d8a4c-ed52-5daa-8d5c-78849cfa8df9
-- title:
--   σ⊗ 1-invariance of semi-local characters
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra and $L/K$ Galois, let $D$ be an idele Galois descent datum for $(\mathcal O_L, K, L)$, that is, a monoid homomorphism $\mathrm{Gal}(L/K) \to \mathrm{RingAut}(\mathbb A_L)$ whose value at each $g$ is continuous and restricts along the structure map $L \to \mathbb A_L$ to $g$ itself, and let $\sigma \in \mathrm{Gal}(L/K)$. Let $\xi_L$ be a monoid homomorphism from the full subgroup $\top$ of $\mathbb A_L^\times$ to $\mathbb C^\times$, and assume that $\xi_L$ is invariant under $\sigma$ in the sense that $\xi_L(\mathrm{unitsAct}\,D\,\sigma\,(z_0)) = \xi_L(z_0)$ for every $z_0 \in \mathbb A_L^\times$, where $\mathrm{unitsAct}\,D\,\sigma$ is the automorphism of $\mathbb A_L^\times$ induced by the ring automorphism $D.\mathrm{act}\,\sigma$. Fix a height-one prime $v$ of $\mathcal O_K$ and a unit $\zeta$ of $L \otimes_K K_v$. The conclusion is that [`TwistedUnipotentTerm.semiLocalCharacter K L ξL v`](def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L38) takes the same value at $\zeta$ and at the image of $\zeta$ under the automorphism of $(L \otimes_K K_v)^\times$ induced by $\sigma \otimes \mathrm{id}_{K_v}$. Here the semi-local character at $v$ is the finite product, over the places $w$ of $L$ with $w$ lying under $v$ equal to $v$, of the values of $\xi_L$ on the determinant of the $\mathrm{GL}_2(\mathbb A_L)$-element $\mathrm{heckeGenAt}$ attached to the $w$-component of $\zeta$ under the base-change identification $L \otimes_K K_v \cong \prod_{w \mid v} L_w$ on units.
--
--   This is the statement that the semi-local component at a finite place $v$ of $K$ of a Galois-invariant idele class character of $L$ is invariant under the semi-local Galois action $\sigma \otimes 1$ on $(L \otimes_K K_v)^\times$. It feeds the evaluation of twisted unipotent orbital terms, being used in [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_semiLocalCharacter_congr_eq_of_forall_unitsAct_eq.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem TwistedUnipotentTerm.semiLocalCharacter_congr_eq_of_forall_unitsAct_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (v : HeightOneSpectrum (𝓞 K)) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    TwistedUnipotentTerm.semiLocalCharacter K L ξL v
        (Units.mapEquiv (Algebra.TensorProduct.congr σ
          (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) =
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ := by sorry
