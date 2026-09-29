-- Prove2me | Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
-- name    : SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/f3ab09be-6d4e-5470-b75e-ae269e1574ed
-- title:
--   The Gaussian e^{-π‖x‖^2} is a Schwartz function
-- statement:
--   Let $\iota$ be a finite type, and let $\mathrm{EuclideanSpace}\ \mathbb{R}\ \iota$ be $\mathbb{R}^{\iota}$ with its Euclidean norm. The assertion is that there exists an element $g$ of the space $\mathcal{S}(\mathbb{R}^{\iota},\mathbb{C})$ of Schwartz maps — that is, a smooth function $\mathbb{R}^{\iota}\to\mathbb{C}$ all of whose iterated Fréchet derivatives satisfy the decay bounds $\sup_x \|x\|^{m}\,\|D^{n}g(x)\| < \infty$ for all $m,n\in\mathbb{N}$ — such that for every $x\in\mathbb{R}^{\iota}$ one has $g(x) = e^{-(\pi\|x\|^{2})}$, the real number $\exp(-(\pi\|x\|^{2}))$ being regarded as a complex number via the canonical inclusion $\mathbb{R}\hookrightarrow\mathbb{C}$. Thus the complex-valued Gaussian of variance normalised so that its Fourier transform is itself lies in the Schwartz class on $\mathbb{R}^{\iota}$; the statement is existential, so no particular packaging of the function as a bundled Schwartz map is fixed by it.
--
--   This records the standard fact that the normalised Gaussian belongs to the Schwartz class on a finite-dimensional Euclidean space, in the bundled form required when Gaussians are used as archimedean test functions. It is used in the construction of adelic Schwartz–Bruhat test functions built from a bottom-row map together with a rational indicator function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq.lean

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped SchwartzMap

theorem SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (ι : Type) [Fintype ι] :
    ∃ g : 𝓢(EuclideanSpace ℝ ι, ℂ), ∀ x : EuclideanSpace ℝ ι,
      g x = ((Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℝ) : ℂ) := by sorry
