-- Prove2me | Theorems.Thm_RatIdele_exists_norm_apply_eq_ideleNorm_rpow
-- name    : RatIdele.exists_norm_apply_eq_ideleNorm_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/64e236c7-9f65-51e9-937a-9ec997ec243a
-- title:
--   Absolute value of an idele class character of ℚ
-- statement:
--   Let $\mu \colon (\mathbb{A}_{\mathbb{Q}})^{\times} \to \mathbb{C}^{\times}$ be a homomorphism of monoids from the unit group of the adele ring of $\mathbb{Q}$ (formed relative to the ring of integers $\mathcal{O}_{\mathbb{Q}}$) to $\mathbb{C}^{\times}$. Assume, first, that $\mu$ satisfies [`AutomorphicForm.IsIdeleClassChar`](def/AutomorphicForm_AdelicLsXi.html#L21), that is, $\mu(\iota(u)) = 1$ for every $u \in \mathbb{Q}^{\times}$, where $\iota$ is the map on units induced by the structure map $\mathbb{Q} \to \mathbb{A}_{\mathbb{Q}}$; so $\mu$ is trivial on the principal ideles and hence factors through the idele class group. Assume, second, that $\mu$ is continuous. Then there exists a real number $\sigma$ such that for every idele $x$ one has $\|\mu(x)\| = (\text{ideleNorm}_{\mathbb{Q}}\, x)^{\sigma}$, the right-hand side being a real power (`rpow`) of $\text{ideleNorm}_{\mathbb{Q}}\, x$, which is by definition the distributive Haar character `distribHaarChar` of the scaling action of $x$ on the adele ring, a non-negative real number, coerced to $\mathbb{R}$. The exponent $\sigma$ is asserted to exist, with no uniqueness claim and no further normalisation.
--
--   This is the first step in the classical description of the quasi-characters of the idele class group of a number field: the absolute value of such a character is a real power of the adelic modulus, so that dividing by that power leaves a unitary character. It is used in the analysis of continuous idele class characters of $\mathbb{Q}$ occurring in the Langlands–Tunnell material, for instance in [`LanglandsTunnell.exists_archCasimir_eigenvector_minimalWeight_of_continuous_realization`](thm.html#LanglandsTunnell.exists_archCasimir_eigenvector_minimalWeight_of_continuous_realization) and in the converse-theorem statements cited alongside it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RatIdele_exists_norm_apply_eq_ideleNorm_rpow.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem RatIdele.exists_norm_apply_eq_ideleNorm_rpow
    (μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 ℚ) ℚ μ) (hc : Continuous μ) :
    ∃ σ : ℝ, ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖((μ x : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm ℚ x ^ σ := by sorry
