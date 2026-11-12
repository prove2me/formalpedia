-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_lemma_26
-- name    : ParallelLpSCO.EpochDA.lemma_26
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:04:28.814767+00:00
-- url     : https://prove2.me/theorems/557a0aa6-fd7b-45a2-9d0c-b993f9f4be3d
-- title:
--   Lemma 26 — the radial penalty $2L(\|x-c\|_p-R)_+$: convex, $3L$-Lipschitz, minimizers in the ball, and a one-query oracle with $q$-th moment at most $(4L)^q$
-- statement:
--   Let $f,g$ satisfy Problem 1 with $L>0$ ($f$ convex on $\mathbb R^d$, $\mathbb E[g(x)]\in\partial f(x)$, $\mathbb E\|g(x)\|_q^q\le L^q$). Let $c\in\mathbb R^d$, $R>0$, and $F(x)=f(x)+2L(\|x-c\|_p-R)_+$. Then:
--   1. $F$ is convex and $3L$-Lipschitz with respect to $\|\cdot\|_p$.
--   2. For $\|y-c\|_p\ge R$ and $y_{c,R}=c+\frac{R}{\|y-c\|_p}(y-c)$: $\|y_{c,R}-c\|_p=R$ and
--   $$f(y_{c,R})\le f(y)+2L(\|y-c\|_p-R)_+-L(\|y-c\|_p-R).$$
--   3. $F$ attains a global minimum. Every global minimizer $x^\star$ satisfies $\|x^\star-c\|_p\le R$ and $F(x^\star)=f(x^\star)=\min_{x\in B_p(c,R)}f(x)$.
--   4. For every deterministic choice $v(x)\in\partial[2L(\|\cdot-c\|_p-R)_+](x)$, the oracle $x\mapsto g(x)+v(x)$ (one query to $g$) is a stochastic subgradient oracle for $F$ with $q$-th moment at most $(4L)^q$.
--
--   It turns the constrained problem over $B_p(c,R)$ into an unconstrained one at constant cost; Theorem 14 applies it with $c=0$.
--
--   **Formalization Note.** Clause 3's "$=\min_{B_p(c,R)}f$" is written as $f(x^\star)\le f(x)$ for all $x\in B_p(c,R)$ (with $\|x^\star-c\|_p\le R$). Clause 4 is `IsGradOracle p (4L) F (g + v)`.
--
--   Differences from the source:
--   - encoding: a stochastic gradient oracle g with E[g(x)] ∈ ∂f(x) and E‖g(x)‖_q^q ≤ L^q (Problem 1) → a jointly measurable map g(x, u) of the query point and one uniform draw u ∈ [0, 1] (`IsGradOracle`); each query uses a fresh draw; reason: every Markov kernel into ℝ^d is the law of such a map, so the class of oracles is the same; measurability in x is the field's standing convention, needed for expectations over random query points
--   - encoding: adding a deterministic subgradient of the penalty to g(x) gives a stochastic subgradient oracle for the penalized function with q-th moment at most (4L)^q, using one query to g → for every selection v with v(x) a subgradient of the penalty at x, (x, u) ↦ g(x, u) + v(x) satisfies IsGradOracle with constant 4L; reason: the one query is visible in the formula; 'every selection' covers the source's arbitrary deterministic choice
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 64, Lemma 26

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics

open MeasureTheory

namespace ParallelLpSCO.EpochDA

/-- Lemma 26 (p. 64). Under Problem 1 with `L > 0`, for `c ∈ ℝ^d` and `R > 0`, the penalized
function `F(x) = f(x) + 2L(‖x − c‖_p − R)_+` is convex and `3L`-Lipschitz for `‖·‖_p`; the radial
projection `y_{c,R}` of a point `y` with `‖y − c‖_p ≥ R` lies on the sphere and satisfies
`f(y_{c,R}) ≤ f(y) + 2L(‖y − c‖_p − R)_+ − L(‖y − c‖_p − R)`; `F` attains its minimum, and every
global minimizer `x⋆` lies in `B_p(c, R)`, has `F(x⋆) = f(x⋆)` and minimizes `f` over `B_p(c, R)`;
and adding any deterministic subgradient `v(x)` of the penalty to `g(x)` gives a Problem 1 oracle
for `F` with constant `4L`. -/
theorem lemma_26 (p : ℝ) (hp : 2 ≤ p) (d : ℕ) (f : Vec d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L : ℝ) (hL : 0 < L) (g : Oracle d) (hg : IsGradOracle p L f g) (c : Vec d) (R : ℝ)
    (hR : 0 < R) :
    let pen : Vec d → ℝ := fun x => 2 * L * max (lpNorm p (x - c) - R) 0
    let F : Vec d → ℝ := fun x => f x + pen x
    (ConvexOn ℝ Set.univ F ∧ ∀ x y, |F x - F y| ≤ 3 * L * lpNorm p (x - y)) ∧
    (∀ y, R ≤ lpNorm p (y - c) →
      lpNorm p ((c + (R / lpNorm p (y - c)) • (y - c)) - c) = R ∧
      f (c + (R / lpNorm p (y - c)) • (y - c)) ≤ f y + pen y - L * (lpNorm p (y - c) - R)) ∧
    (∃ xstar, ∀ x, F xstar ≤ F x) ∧
    (∀ xstar, (∀ x, F xstar ≤ F x) →
      lpNorm p (xstar - c) ≤ R ∧ F xstar = f xstar ∧ ∀ x ∈ lpBall p c R, f xstar ≤ f x) ∧
    (∀ v : Vec d → Vec d, (∀ x, IsSubgrad pen x (v x)) →
      IsGradOracle p (4 * L) F (fun x u => g x u + v x)) := by sorry

end ParallelLpSCO.EpochDA
