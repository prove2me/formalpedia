-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_fdGradient_random_point_epsSubgrad
-- name    : QAlgorithms.Nannicini.fdGradient_random_point_epsSubgrad
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:46:18.530294+00:00
-- url     : https://prove2.me/theorems/c5a8b117-8af0-4686-b020-743e66744040
-- title:
--   Finite differences of an approximate function at a random point give an explicit ϵ′-subgradient at the origin (corrected)
-- statement:
--   This is a corrected form of Proposition 5.31; the changes are listed in the Formalization Note.
--
--   Let $d \ge 0$ and $r, L, \epsilon, \delta \in \mathbb{R}$ with $r > 0$, $L > 0$, $0 < \delta < 1/3$ and $0 < \epsilon < rL\sqrt d/\delta$. Write $B_\infty(0,s) = \{x \in \mathbb{R}^d : |x_i| \le s \text{ for all } i\}$. Let $f : \mathbb{R}^d \to \mathbb{R}$ be convex and $L$-Lipschitz on $B_\infty(0,2r)$ with respect to the Euclidean norm, and let $\tilde f : \mathbb{R}^d \to \mathbb{R}$ satisfy $|f(x) - \tilde f(x)| \le \epsilon$ for all $x \in B_\infty(0,2r)$. Let $\eta$ be any step with $0 < \eta < r$, let
--
--   $$
--   \nabla^{(\eta)} \tilde f(z)_j = \frac{\tilde f(z+\eta e_j) - \tilde f(z-\eta e_j)}{2\eta}
--   $$
--
--   be the finite-difference gradient of $\tilde f$, and set
--
--   $$
--   \epsilon' = 2Lr\sqrt d + \frac{\eta d L}{\delta} + \frac{2 r d \epsilon}{\eta}.
--   $$
--
--   Then $\epsilon' > \epsilon$, and for $z$ drawn uniformly at random from $B_\infty(0,r)$, with probability at least $1 - \delta$ the vector $g = \nabla^{(\eta)} \tilde f(z)$ is an $\epsilon'$-subgradient of $f$ at $0$ on $B_\infty(0,2r)$:
--
--   $$
--   f(x) \ge f(0) + \langle g, x\rangle - \epsilon' \qquad \text{for all } x \in B_\infty(0,2r).
--   $$
--
--   More precisely, there is a measurable set $S \subseteq B_\infty(0,r)$ with $\operatorname{vol}(S) \ge (1-\delta)\operatorname{vol}(B_\infty(0,r))$ such that the inequality holds for every $z \in S$.
--
--   This is the classical step of building a separation oracle from a membership oracle: a finite-difference gradient of the approximately evaluated height function at a random point near the origin gives an approximate subgradient at the origin.
--
--   **Formalization Note** Three corrections to the printed statement. (1) The finite differences are taken of $\tilde f$ rather than $f$: as printed, $\tilde f$ plays no role, while the preceding text says the estimate, not the exact value, is used. (2) The $\epsilon'$-subgradient inequality is required on $B_\infty(0,2r)$, where the hypotheses control $f$ and $\tilde f$. Over all of $\mathbb{R}^d$ (Def. 5.24) the claim is false: for linear $f$ a perturbation $\tilde f$ yields $\nabla f + e$ with $e \ne 0$, and $\langle e, x\rangle$ is unbounded. (3) The source never gives $\eta$ or $\epsilon'$. The statement holds for every $\eta \in (0,r)$ with the explicit $\epsilon'$ above, built from the proof sketch's steps (Lemmas 5.28 and 5.30, Markov's inequality, the $\tilde f$ error, and the closeness of $z$ to $0$). The probability is the Lebesgue inner measure of the good event, since $\tilde f$ need not be measurable. The subgradient is the linear form $x \mapsto \sum_j g_j x_j$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 122, Proposition 5.31. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open MeasureTheory




/-- Corrected statement. Nannicini p.122, Proposition 5.31 (Lem. 12 in van Apeldoorn et al.
2020a). Printed: let `r > 0`, `L > 0`, `0 < δ < 1/3`, `0 < ϵ < rL√d/δ`, `f : ℝ^d → ℝ` convex and
`L`-Lipschitz on `B_∞(0, 2r)`, `f̃` with `|f(x) − f̃(x)| ≤ ϵ` on `B_∞(0, 2r)`; then for a uniformly
random `z ∈ B_∞(0, r)` "we can compute parameters `0 < η < r`, `ϵ′ > ϵ`" such that with probability
at least `1 − δ`, `∇^(η) f(z) ∈ ∂_ϵ′ f(0)`.

Changes, and why the printed version cannot be stated as is:
1. The finite differences are taken of `f̃`, not `f`: as printed `f̃` plays no role, while the text
   just before (p.122) says the finite-difference approximation uses the estimate of the function,
   not its exact value.
2. The `ϵ′`-subgradient inequality (Def. 5.24) is required on `B_∞(0, 2r)`, the set on which the
   hypotheses control `f` and `f̃`, not on all of `ℝ^d`. Over `ℝ^d` the claim is false: for linear
   `f` and a perturbation `f̃`, `∇^(η) f̃(z) = ∇f + e` with `e ≠ 0`, and `⟨e, x⟩` is unbounded.
3. `η` and `ϵ′` are never given (the proof omits the "cumbersome expressions"). The statement holds
   for every `η ∈ (0, r)` (the source's only condition on `η`), with the explicit
   `ϵ′ = 2Lr√d + ηdL/δ + 2rdϵ/η`, assembled from the proof sketch's steps: Lemma 5.28 and 5.30
   (gradient error `ηdL/(2r)` in expectation), Markov's inequality (error `≤ ηdL/(2rδ)` with
   probability `1 − δ`), the `f̃` error `dϵ/η` in ℓ1, and "z and 0 are close and f is
   L-Lipschitz" (the term `2Lr√d`). This constant is the drafter's instantiation of the sketch.
4. "With probability at least `1 − δ`" for a uniformly random `z` is stated as a measurable
   `S ⊆ B_∞(0, r)` of Lebesgue measure at least `(1 − δ) vol(B_∞(0, r))` on which the conclusion
   holds (since `f̃` is arbitrary, the event itself need not be measurable).

The Lipschitz condition uses the Euclidean norm (the book's convention, p.11). -/
theorem fdGradient_random_point_epsSubgrad {d : ℕ} (r L ϵ δ : ℝ) (hr : 0 < r) (hL : 0 < L)
    (hδ0 : 0 < δ) (hδ : δ < 1 / 3) (hϵ0 : 0 < ϵ) (hϵ : ϵ < r * L * Real.sqrt d / δ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hLip : ∀ y ∈ {y : Fin d → ℝ | ∀ i, |y i| ≤ 2 * r},
      ∀ y' ∈ {y : Fin d → ℝ | ∀ i, |y i| ≤ 2 * r},
        |f y - f y'| ≤ L * Real.sqrt (∑ i, (y i - y' i) ^ 2))
    (ft : (Fin d → ℝ) → ℝ) (hft : ∀ x ∈ {x : Fin d → ℝ | ∀ i, |x i| ≤ 2 * r}, |f x - ft x| ≤ ϵ)
    (η : ℝ) (hη0 : 0 < η) (hηr : η < r) :
    ϵ < 2 * L * r * Real.sqrt d + η * d * L / δ + 2 * r * d * ϵ / η ∧
    ∃ S ⊆ {z : Fin d → ℝ | ∀ i, |z i| ≤ r}, MeasurableSet S ∧
      (1 - δ) * volume.real {z : Fin d → ℝ | ∀ i, |z i| ≤ r} ≤ volume.real S ∧
      ∀ z ∈ S, IsEpsSubgradOn {x : Fin d → ℝ | ∀ i, |x i| ≤ 2 * r} f
        (2 * L * r * Real.sqrt d + η * d * L / δ + 2 * r * d * ϵ / η) 0
        (∑ j : Fin d, fdGradient η ft z j • (LinearMap.proj j : (Fin d → ℝ) →ₗ[ℝ] ℝ)) := by
  sorry

end QAlgorithms.Nannicini
