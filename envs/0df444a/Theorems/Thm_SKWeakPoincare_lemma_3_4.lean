-- Prove2me | Theorems.Thm_SKWeakPoincare_lemma_3_4
-- name    : SKWeakPoincare.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:07.186669+00:00
-- url     : https://prove2.me/theorems/7273a8ae-6d0c-4779-89e8-664a0d3a1ca8
-- title:
--   Lemma 3.4 — Grönwall and path comparison for $Y_t=\omega_t+\int_0^tb(Y_s)\,ds$
-- statement:
--   Fix $T>0$.
--
--   1. Let $a,L\ge0$ and let $d:[0,T]\to[0,\infty)$ be continuous. If $d(t)\le a+L\int_0^td(s)\,ds$ for every $t\in[0,T]$, then $d(t)\le a\,e^{Lt}$ for every $t\in[0,T]$.
--   2. Let $b:\mathbb R^n\to\mathbb R^n$ be globally $L$-Lipschitz, and let $Y^\omega$ denote a solution of $Y^\omega_t=\omega_t+\int_0^tb(Y^\omega_s)\,ds$, $0\le t\le T$. For all $\omega,\omega'\in C_0([0,T];\mathbb R^n)$,
--   $$
--   \|Y^{\omega'}-Y^\omega\|_\infty\le e^{LT}\|\omega'-\omega\|_\infty .
--   $$
--   3. For all $\omega\in C_0([0,T];\mathbb R^n)$ and $h\in H_T$,
--   $$
--   \|Y^{\omega+h}-Y^\omega\|_\infty\le\sqrt T\,e^{LT}\|h\|_{H_T}.
--   $$
--
--   The lemma transfers bounds on driving paths to bounds on solutions of the localization equation.
--
--   **Formalization Note** Norms are Euclidean, and $\|\cdot\|_\infty$ is the norm of the path space. $h\in H_T$ is written $h_s=\int_0^sg$ with $\|h\|_{H_T}=$ `cmNorm T g`.
--
--   Differences from the source:
--   - encoding: a continuous d : [0,T] → [0,∞) → d : ℝ → ℝ, ContinuousOn d [0,T] and 0 ≤ d on [0,T]; reason: only the values on [0,T] enter
--   - encoding: L ≥ 0 a real constant, and b globally L-Lipschitz on ℝⁿ → L : ℝ≥0 and LipschitzWith L b on EuclideanSpace ℝ (Fin n); reason: same constants; the Euclidean norm is the paper's ‖·‖₂
--   - encoding: the solutions Y^ω of the integral equation → any paths Y, Y' with IsLocPath b ω Y and IsLocPath b ω' Y'; reason: for Lipschitz b the solution exists and is unique
--   - encoding: h ∈ H_T with norm ‖h‖_{H_T} → IsCMShift g h with norm cmNorm T g; reason: h ∈ H_T iff h = ∫₀ˢ g with g ∈ L²([0,T]), and then ‖h‖_{H_T} = ‖g‖_{L²}
--   - encoding: ω, ω' ∈ C₀([0,T];ℝⁿ) → paths of C([0,T];ℝⁿ) with pathExt ω 0 = 0; reason: C₀ is that subset
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Lemma 3.4, p.16

import Mathlib
import Definitions.Def_SKWeakPoincare_PathSpace

open MeasureTheory
open scoped NNReal

namespace SKWeakPoincare

/-- **Lemma 3.4 (Grönwall and path comparison).**
Hou–Liu–Yu, *Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy
for the Sherrington–Kirkpatrick model*, arXiv:2610.09882, Lemma 3.4, p. 16.

Fix `T > 0`. (a) Let `a, L ≥ 0` and `d : [0, T] → [0, ∞)` be continuous. If
`d(t) ≤ a + L ∫₀ᵗ d(s) ds` for every `t ∈ [0, T]`, then `d(t) ≤ a exp(Lt)`.
For a globally `L`-Lipschitz `b : ℝ^n → ℝ^n`, the solutions of `Y^ω_t = ω_t + ∫₀ᵗ b(Y^ω_s) ds`
satisfy, for all `ω, ω' ∈ C₀([0, T]; ℝ^n)` and `h ∈ H_T`,
(b) `‖Y^{ω'} − Y^ω‖_∞ ≤ exp(LT) ‖ω' − ω‖_∞` and
(c) `‖Y^{ω+h} − Y^ω‖_∞ ≤ √T exp(LT) ‖h‖_{H_T}`.

**Formalization Note.** `ℝ^n` is `EuclideanSpace ℝ (Fin n)`, so the Lipschitz condition and the norm
`‖·‖_∞ = sup_t ‖·‖₂` of `PathSpace T n` are Euclidean. `ω ∈ C₀` is `pathExt ω 0 = 0`; `h ∈ H_T` with
`‖h‖_{H_T} = cmNorm T g` is `IsCMShift g h`. "The solutions" are any paths solving the equation
(`IsLocPath`); for Lipschitz `b` they exist and are unique. -/
theorem lemma_3_4 (T : ℝ) (hT : 0 < T) (n : ℕ) (L : ℝ≥0) :
    (∀ (a : ℝ) (d : ℝ → ℝ), 0 ≤ a → ContinuousOn d (Set.Icc 0 T) →
      (∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ d t) →
      (∀ t ∈ Set.Icc (0 : ℝ) T, d t ≤ a + (L : ℝ) * ∫ s in (0 : ℝ)..t, d s) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, d t ≤ a * Real.exp ((L : ℝ) * t)) ∧
    (∀ b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), LipschitzWith L b →
      (∀ ω ω' Y Y' : PathSpace T n, pathExt ω 0 = 0 → pathExt ω' 0 = 0 →
        IsLocPath b ω Y → IsLocPath b ω' Y' →
        ‖Y' - Y‖ ≤ Real.exp ((L : ℝ) * T) * ‖ω' - ω‖) ∧
      (∀ (ω h Y Yh : PathSpace T n) (g : ℝ → EuclideanSpace ℝ (Fin n)),
        pathExt ω 0 = 0 → IsCMShift g h → IsLocPath b ω Y → IsLocPath b (ω + h) Yh →
        ‖Yh - Y‖ ≤ Real.sqrt T * Real.exp ((L : ℝ) * T) * cmNorm T g)) := by sorry

end SKWeakPoincare
