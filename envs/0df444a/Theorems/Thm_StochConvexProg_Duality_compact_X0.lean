-- Prove2me | Theorems.Thm_StochConvexProg_Duality_compact_X0
-- name    : StochConvexProg.Duality.compact_X0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:16:59.008831+00:00
-- url     : https://prove2.me/theorems/2025e292-ea4e-43a1-9f25-2d54da3137f1
-- title:
--   (4.9) — with C₁, C₂ bounded, X₀ is weakly compact in X and X₀′ is σ(ℒ^∞, ℒ¹)-compact
-- statement:
--   Assume the standing assumptions, $\sigma$ a probability measure, and that $C_1$ and $C_2$ are bounded. Let
--   $$X_0=\{x=(x_1,x_2)\in X: x_1\in C_1\text{ and almost surely }x_2(s)\in C_2\},\qquad X_0'=\{x_2\in\mathcal L^\infty_{n_2}: x_2(s)\in C_2\text{ almost surely}\}.$$
--   Then
--
--   1. $X_0$ is compact in the weak topology induced on $X$ by $V=\mathbb R^{n_1}\times\mathcal L^1_{n_2}$ through the pairing (2.11), and
--   2. $X_0'$ is compact in the weak topology induced on $\mathcal L^\infty_{n_2}$ by $\mathcal L^1_{n_2}$.
--
--   This compactness is the step in the proof of Theorem 3 that makes the infimum defining the perturbation function attained and its lower semicontinuity pass from $F$ to $\varphi$.
--
--   **Formalization Note** The weak topologies are the coarsest topologies making the pairings with $V$ (resp. $\mathcal L^1_{n_2}$) continuous; they are passed explicitly, never the norm topology (in which $X_0'$ is in general not compact).
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), pp. 189–190, proof of Theorem 3, (4.9)

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual

open MeasureTheory

namespace StochConvexProg.Duality

/-- Rockafellar–Wets (1976), pp. 189–190, proof of Theorem 3, (4.9): with `C₁`, `C₂` bounded,
`X₀` is compact in the weak topology induced on `X` by `V`, and `X₀′` is compact in the weak
topology induced on `ℒ^∞_{n₂}` by `ℒ¹_{n₂}`. -/
theorem compact_X0 {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂)
    (hC₁ : Bornology.IsBounded pr.C₁) (hC₂ : Bornology.IsBounded pr.C₂) :
    @IsCompact (XSpace σ n₁ n₂) (weakX σ n₁ n₂) pr.X₀ ∧
      @IsCompact (Lp (Fin n₂ → ℝ) ⊤ σ) (weakLinf σ n₂) pr.X₀' := by sorry

end StochConvexProg.Duality
