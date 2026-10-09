-- Prove2me | Theorems.Thm_UnifiedFBSDE_Main_theorem_2_3
-- name    : UnifiedFBSDE.Main.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:11.2988+00:00
-- url     : https://prove2.me/theorems/118b5710-f516-4aae-ae8a-069fe3da87e1
-- title:
--   Theorem 2.3, p. 7 — a decoupling field gives a unique solution of the FBSDE (1.1) over [0, T] with Y_t = u(t, X_t)
-- statement:
--   Let $T>0$ and let the FBSDE (1.1) on $[0,T]$, driven by a one-dimensional Brownian motion with its augmented natural filtration, satisfy Assumption 2.1. Suppose $u$ is a decoupling field of (1.1) in the sense of Definition 2.2. Then for every initial state $x\in\mathbb R$ the FBSDE (1.1) has a unique solution $\Theta=(X,Y,Z)\in\mathbb L^2$, and every solution satisfies
--
--   $$
--   Y_t=u(t,X_t),\qquad t\in[0,T],\ \mathbb P\text{-a.s.}\tag{1.4}
--   $$
--
--   The theorem reduces global well-posedness to the existence of a decoupling field: solutions on the short intervals of Definition 2.2 are patched together along a partition of $[0,T]$.
--
--   **Formalization Note** Uniqueness is in $\mathbb L^2$, the class in which Definition 2.2 provides uniqueness on each subinterval; the identity (1.4) holds a.s. for each fixed $t$.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 7, Theorem 2.3

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_UnifiedFBSDE_Main_Setting

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace UnifiedFBSDE.Main

theorem theorem_2_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B)
    (T : ℝ≥0) (hT : 0 < T) (K₀ : ℝ) (c : Coeffs Ω)
    (hA : Assumption21 (ReflectedBSDE.Existence.augmentedFiltration P hB) P T K₀ c)
    (u : ℝ≥0 → ℝ → Ω → ℝ)
    (hu : IsDecouplingField (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T u) :
    ∀ x : ℝ, HasUniqueSolution (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T x ∧
      ∀ X Y Z : ℝ≥0 → Ω → ℝ,
        SolvesFBSDE (ReflectedBSDE.Existence.augmentedFiltration P hB) P B c T x X Y Z →
          ∀ t ≤ T, ∀ᵐ ω ∂P, Y t ω = u t (X t ω) ω := by sorry

end UnifiedFBSDE.Main
