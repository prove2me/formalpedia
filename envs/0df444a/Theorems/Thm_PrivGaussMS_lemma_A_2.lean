-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_A_2
-- name    : PrivGaussMS.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:51.047119+00:00
-- url     : https://prove2.me/theorems/18bf54f5-57ec-443b-ba5e-f420777bb433
-- title:
--   Lemma A.2 — postprocessing and successive private calls
-- statement:
--   Let $\varepsilon,\delta,\varepsilon_1,\delta_1,\varepsilon_2,\delta_2\ge0$.
--
--   1. Postprocessing an $(\varepsilon,\delta)$-private output by a fixed randomized rule that does not access the input preserves privacy.
--   2. Suppose $M_1$ is $(\varepsilon_1,\delta_1)$-private and, for every fixed $y$, $M_2(\cdot,y)$ is $(\varepsilon_2,\delta_2)$-private. Using fresh randomness for the second call, draw $Y_1=M_1(x)$ and then $Y_2=M_2(x,Y_1)$. The joint release $(Y_1,Y_2)$ is $(\varepsilon_1+\varepsilon_2,\delta_1+\delta_2)$-private.
--
--   Differences from the source:
--   - encoding: a fixed randomized rule; the second call M₂(x, ·) → a Markov kernel K; for each x a Markov kernel y ↦ M₂(x, y), the joint release being M₁(x) ⊗ₘ M₂(x, ·); reason: randomized maps between measurable spaces
--   - encoding: a randomized mechanism and its output law → a family of output laws, with IsDPM asserting that each is a probability measure and applying the published IsDP; reason: Lean pushes a non-measurable map to the zero measure, under which DP would hold vacuously; the assertion rules this out and changes no instance
--   - encoding: ε, δ ≥ 0 → all privacy parameters nonnegative; reason: the paper's DP parameter range (p.24)
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma A.2, p.24

import Mathlib
import Definitions.Def_PrivGaussMS_Basics

open MeasureTheory ProbabilityTheory

namespace PrivGaussMS

/-- **Lemma A.2** (Postprocessing and successive private calls), Moayedi, Yassaee, Ebrahimi,
*Optimal Private Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…),
p.24.

1. Postprocessing an `(ε, δ)`-private output by a fixed randomized rule `K` that does not access
   the input preserves privacy.
2. If `M₁` is `(ε₁, δ₁)`-private and `M₂(·, y)` is `(ε₂, δ₂)`-private for every fixed `y`, the
   joint release `(Y₁, Y₂)`, `Y₁ = M₁(x)`, `Y₂ = M₂(x, Y₁)` with fresh randomness, is
   `(ε₁ + ε₂, δ₁ + δ₂)`-private.

**Formalization Note.** Mechanisms are families of output laws (`IsDPM`, the published `IsDP`).
The postprocessing rule is a Markov kernel; the second call is, for each input `x`, a Markov
kernel `y ↦ M₂(x, y)`, and the joint release is `M₁(x) ⊗ₘ M₂(x, ·)`. Parameters are nonnegative,
as in the paper's DP definition ("For `ε, δ ≥ 0`", p.24). -/
theorem lemma_A_2 {X Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] {n : ℕ}
    (M : (Fin n → X) → Measure Y) (K : Kernel Y Z) [IsMarkovKernel K]
    (M₁ : (Fin n → X) → Measure Y) (M₂ : (Fin n → X) → Kernel Y Z)
    [∀ x, IsMarkovKernel (M₂ x)]
    (ε δ ε₁ δ₁ ε₂ δ₂ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hε₁ : 0 ≤ ε₁) (hδ₁ : 0 ≤ δ₁)
    (hε₂ : 0 ≤ ε₂) (hδ₂ : 0 ≤ δ₂) :
    (IsDPM M ε δ → IsDPM (fun x => (M x).bind K) ε δ) ∧
    (IsDPM M₁ ε₁ δ₁ → (∀ y, IsDPM (fun x => M₂ x y) ε₂ δ₂) →
      IsDPM (fun x => M₁ x ⊗ₘ M₂ x) (ε₁ + ε₂) (δ₁ + δ₂)) := by sorry

end PrivGaussMS
