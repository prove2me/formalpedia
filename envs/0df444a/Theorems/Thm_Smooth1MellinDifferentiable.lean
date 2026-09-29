-- Prove2me | Theorems.Thm_Smooth1MellinDifferentiable
-- name    : Smooth1MellinDifferentiable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:37:05.076595+00:00
-- url     : https://prove2.me/theorems/80645e1f-3942-4989-9ac7-401b0c07ac0b
-- title:
--   Holomorphy of the Mellin transform of the smoothed cutoff on $\mathrm{Re}(s) > 0$
-- statement:
--   Let $\Psi$ be a smoothing kernel of class $C^1$, supported in $[1/2, 2]$, nonnegative on $(0, \infty)$, with multiplicative mass one $\int_0^\infty \Psi(x)\, dx / x = 1$, and fix $\epsilon \in (0, 1)$. Let $\widetilde{1_\epsilon} = \mathrm{Smooth1}\,\Psi\,\epsilon$ be the smoothed indicator of $(0, 1]$ built from $\Psi$, viewed as a complex-valued function on $(0, \infty)$.
--
--   Then the Mellin transform of the smoothed cutoff is complex-differentiable at every point of the right half-plane: for each $s \in \mathbb{C}$ with $\mathrm{Re}(s) > 0$,
--
--   $$s \;\longmapsto\; \mathcal{M}\big(\widetilde{1_\epsilon}\big)(s) = \int_0^\infty \widetilde{1_\epsilon}(x)\, x^{s-1}\, dx$$
--
--   is differentiable at $s$; in particular $\mathcal{M}(\widetilde{1_\epsilon})$ is holomorphic on $\{\mathrm{Re}(s) > 0\}$.
--
--   Holomorphy of this Mellin transform is essential for the contour-shifting arguments of the smoothed Prime Number Theorem proof: the integrand $-\tfrac{\zeta'}{\zeta}(s)\, \mathcal{M}(\widetilde{1_\epsilon})(s)\, X^s$ must be analytic away from the pole of $\zeta'/\zeta$ at $s = 1$ and the zeros of $\zeta$ for Cauchy's theorem to move the line of integration into the zero-free region.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L1041-L1063

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_MellinCalculus_defs

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

-- TODO: generalize to `RCLike`

local notation (name := mellintransform) "𝓜" => mellin

-- filter-free version:

-- This lemma might not be necessary, but the RHS is supported on [0, infinity), which makes
-- results like `support_MellinConvolution_subsets` easier to apply.

/-% ** Wrong delimiters on purpose, no need to include this in the LaTeX outline
\begin{lemma}[Smooth1Properties_estimate]\label{Smooth1Properties_estimate}
\lean{Smooth1Properties_estimate}\leanok
For $\epsilon>0$,
$$
  \log2>\frac{1-2^{-\epsilon}}\epsilon
$$
\end{lemma}
%-/

theorem Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (𝓜 (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by sorry
