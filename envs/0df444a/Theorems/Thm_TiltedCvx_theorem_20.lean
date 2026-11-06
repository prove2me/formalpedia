-- Prove2me | Theorems.Thm_TiltedCvx_theorem_20
-- name    : TiltedCvx.theorem_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:41:26.030083+00:00
-- url     : https://prove2.me/theorems/8bd35e7c-a14f-4df7-b2c4-7fbc00bd6a4c
-- title:
--   Theorem 20 — characterizations of $\gamma$-tilted secant convexity
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper and lower semicontinuous with $K:=\operatorname{dom}(f)$, and let $\gamma\in(0,1]$. The following are equivalent.
--
--   1. $f$ is $\gamma$–tilted secant convex.
--   2. For all $y,z\in K$ and $\lambda\in(0,1)$, with $x=\lambda y+(1-\lambda)z$,
--   $$
--   \lambda\,\bar\psi_{\sqrt\gamma}\big(f(y)-f(x)\big)+(1-\lambda)\,\bar\psi_{\sqrt\gamma}\big(f(z)-f(x)\big)\ge0 .
--   $$
--   3. For every $m\ge2$, all $y_1,\dots,y_m\in K$ and every $\lambda\in\Delta_m$,
--   $$
--   f\Big(\sum_{i=1}^m\lambda_iy_i\Big)\le M^{(m)}_{\gamma,\lambda}\big(f(y_1),\dots,f(y_m)\big).
--   $$
--   4. For every $m\ge2$, all $y_1,\dots,y_m\in K$ and all $\lambda_1,\dots,\lambda_m>0$ with $\sum_i\lambda_i=1$, with $x=\sum_i\lambda_iy_i$,
--   $$
--   \sum_{i=1}^m\lambda_i\,\bar\psi_{\sqrt\gamma}\big(f(y_i)-f(x)\big)\ge0 .
--   $$
--   5. $K$ is convex and there is an operator $F:\mathbb R^d\rightrightarrows\mathbb R^d$ with $\operatorname{ri}(K)\subseteq\operatorname{dom}(F)$ such that $f$ is $\sqrt\gamma$–tilted convex with respect to $F$.
--
--   Furthermore, the equivalence of 1–4 holds even if $f$ is not assumed lower semicontinuous.
--
--   **Formalization Note** The statement is given for every proper $f$: items 1–4 are equivalent, and if $f$ is also lsc then 1 ⇔ 5. Together these are exactly the theorem and its last sentence. Differences $f(y_i)-f(x)$ are extended-real, so (2) and (4) fail when $f(x)=+\infty$, as in the paper's arithmetic. $\Delta_m$ is $\lambda_i\ge0$, $\sum\lambda_i=1$; indices are `Fin m`.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: (i)–(v) equivalent for proper lsc f; (i)–(iv) equivalent without lsc → TFAE (i)–(iv) for proper f, and (i) ↔ (v) for proper lsc f; reason: logically equivalent packaging of the two assertions
--   - encoding: f(y) − f(x) in the extended reals → EReal subtraction; reason: a real minus +∞ is −∞ in both; values at points of K are real
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 20, p.27

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_psiBar
import Definitions.Def_TiltedCvx_TiltedConvexWrt
import Definitions.Def_TiltedCvx_TiltedSecant
import Definitions.Def_TiltedCvx_expectileMean

namespace TiltedCvx

/-- **Theorem 20 (characterizations of γ–tilted secant convexity).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 20, p.27. Let `f : ℝ^d → ℝ̄` be proper
lsc with `K := dom(f)`, and `γ ∈ (0, 1]`. The following are equivalent:
(i) `f` is γ–tilted secant convex;
(ii) for every `y, z ∈ K` and `λ ∈ (0, 1)`,
`λ ψ̄√γ(f(y) − f(x)) + (1 − λ) ψ̄√γ(f(z) − f(x)) ≥ 0`, `x = λy + (1 − λ)z` (20);
(iii) for every `m ≥ 2`, `y₁, …, y_m ∈ K` and `λ ∈ Δm`,
`f(Σ λᵢyᵢ) ≤ M^{(m)}_{γ,λ}(f(y₁), …, f(y_m))` (21);
(iv) for every `m ≥ 2`, `y₁, …, y_m ∈ K` and `λ₁, …, λ_m > 0` with `Σ λᵢ = 1`,
`Σ λᵢ ψ̄√γ(f(yᵢ) − f(x)) ≥ 0`, `x = Σ λᵢyᵢ` (22);
(v) `K` is convex and there is `F : ℝ^d ⇒ ℝ^d` with `ri(K) ⊆ dom(F)` such that `f` is
√γ–tilted convex with respect to `F`.
Furthermore, the equivalence of (i)–(iv) holds even if `f` is not assumed lsc.

**Formalization Note** Stated for every proper `f`: (i)–(iv) are equivalent, and if `f` is also
lsc then (i) ⇔ (v); together these are the theorem and its last sentence. The differences
`f(yᵢ) − f(x)` are taken in `EReal` (if `f(x) = +∞` they are `−∞`, and (20), (22) fail, as in the
paper's extended arithmetic). `Δm` is `λᵢ ≥ 0`, `Σ λᵢ = 1`; indices are `Fin m`. -/
theorem theorem_20 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : IsProper f) :
    List.TFAE
      [TiltedSecant γ f,
       ∀ y ∈ effDom f, ∀ z ∈ effDom f, ∀ l : ℝ, 0 < l → l < 1 →
         0 ≤ (l : EReal) * psiBar (Real.sqrt γ) (f y - f (l • y + (1 - l) • z)) +
           ((1 - l : ℝ) : EReal) * psiBar (Real.sqrt γ) (f z - f (l • y + (1 - l) • z)),
       ∀ m : ℕ, 2 ≤ m → ∀ ys : Fin m → E, (∀ i, ys i ∈ effDom f) →
         ∀ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) → ∑ i, lam i = 1 →
           f (∑ i, lam i • ys i) ≤
             ((expectileMean γ lam (fun i => (f (ys i)).toReal) : ℝ) : EReal),
       ∀ m : ℕ, 2 ≤ m → ∀ ys : Fin m → E, (∀ i, ys i ∈ effDom f) →
         ∀ lam : Fin m → ℝ, (∀ i, 0 < lam i) → ∑ i, lam i = 1 →
           0 ≤ ∑ i, (lam i : EReal) *
             psiBar (Real.sqrt γ) (f (ys i) - f (∑ j, lam j • ys j))] ∧
    (LowerSemicontinuous f →
      (TiltedSecant γ f ↔
        Convex ℝ (effDom f) ∧
          ∃ F : E → Set E, (∀ x ∈ intrinsicInterior ℝ (effDom f), (F x).Nonempty) ∧
            TiltedConvexWrt (Real.sqrt γ) f F)) := by sorry

end TiltedCvx
