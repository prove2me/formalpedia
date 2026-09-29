-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_continuous_semiLocalCharacter_of_continuous
-- name    : TwistedUnipotentTerm.continuous_semiLocalCharacter_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/16834891-7a00-5bdc-8c9b-6615627f0598
-- title:
--   Continuity of the semi-local character at a finite place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\xi_L$ be a monoid homomorphism from the full subgroup $\top$ of $(\mathbb{A}_L)^\times$, the units of the adele ring of $\mathcal{O}_L$ over $L$, to $\mathbb{C}^\times$, and assume that the composite $z \mapsto \xi_L(z) \in \mathbb{C}$, defined on all of $(\mathbb{A}_L)^\times$ by viewing each $z$ as an element of $\top$, is continuous. Let $v$ be a height-one prime of $\mathcal{O}_K$. The conclusion is that the function [`TwistedUnipotentTerm.semiLocalCharacter K L ξL v`](def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L38) on $(L \otimes_K K_v)^\times$ is continuous; here its value at $\zeta$ is the finite product, over the set of height-one primes $w$ of $\mathcal{O}_L$ lying under $v$ (the extensions of $v$), of the complex numbers $\xi_L$ evaluated at the determinant of [`NumberField.AdelicLevel.heckeGenAt`](def/NumberField_AdelicLevel.html#L708) applied to the $w$-component of $\zeta$, that is, of the image of $\zeta$ under the units map of the base-change isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$ followed by projection to the factor at $w$; `heckeGenAt` sends a unit of $L_w$ to the element $\mathrm{diag}(a,1)$ of $\mathrm{GL}_2(\mathbb{A}_L)$ whose entry is the given local unit placed at $w$ and $1$ elsewhere.
--
--   This is the continuity of the semi-local restriction at $v$ of an idele class character, written multiplicatively over the primes of $L$ above $v$ and realised through determinants of Hecke generators. It is used in the analysis of twisted unipotent orbital terms, where the semi-local character is integrated against local Haar measures, and is cited by [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_continuous_semiLocalCharacter_of_continuous.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem TwistedUnipotentTerm.continuous_semiLocalCharacter_of_continuous
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (TwistedUnipotentTerm.semiLocalCharacter K L ξL v) := by sorry
