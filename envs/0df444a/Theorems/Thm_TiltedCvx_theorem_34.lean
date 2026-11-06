-- Prove2me | Theorems.Thm_TiltedCvx_theorem_34
-- name    : TiltedCvx.theorem_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:40:52.1001+00:00
-- url     : https://prove2.me/theorems/0bae9abe-6e6f-4cca-a15a-fdad69c81f35
-- title:
--   Theorem 34 — approximate mean values for lsc functions
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper and lower semicontinuous, let $x\neq y$ be points of $\operatorname{dom}(f)$, and for $\lambda\in[0,1]$ put $z_\lambda=\lambda x+(1-\lambda)y$. Then there are $\lambda\in[0,1)$ with $z_\lambda\in\operatorname{dom}(f)$, a sequence $x_k\to z_\lambda$ with $f(x_k)\to f(z_\lambda)$, and Fréchet subgradients $v_k\in\hat\partial f(x_k)$ such that
--
--   $$
--   \frac{1}{1-\lambda}\limsup_{k\to\infty}\langle v_k,x_k-x\rangle\le f(y)-f(x)\qquad\text{and}\qquad\limsup_{k\to\infty}\langle v_k,y-x\rangle\le f(y)-f(x).
--   $$
--
--   Similarly, there are $\lambda'\in(0,1]$ with $z_{\lambda'}\in\operatorname{dom}(f)$, $x'_k\to z_{\lambda'}$ with $f(x'_k)\to f(z_{\lambda'})$, and $v'_k\in\hat\partial f(x'_k)$ such that
--
--   $$
--   f(y)-f(x)\le\frac{1}{\lambda'}\liminf_{k\to\infty}\langle v'_k,y-x'_k\rangle\qquad\text{and}\qquad f(y)-f(x)\le\liminf_{k\to\infty}\langle v'_k,y-x\rangle.
--   $$
--
--   This nonsmooth mean-value inequality replaces the classical mean value theorem in the passage from subgradient conditions to inequalities between function values.
--
--   **Formalization Note** The upper and lower limits are taken in the extended reals, so they exist without boundedness, and the factors $1/(1-\lambda)$, $1/\lambda'$ multiply them there.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: lim sup / lim inf of ⟨v_k, ·⟩ → Filter.limsup / liminf in EReal of the real inner products; reason: the paper's limits are extended-real; a real limsup would be junk 0 for unbounded sequences
--   - encoding: x_k →^f z (f-attentive convergence, p.11) → x_k → z and f(x_k) → f(z) in EReal; reason: the definition on p.11
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 34, p.51

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_NAPPAL_VPEB_frechetSubdiff

open Filter Topology
open scoped InnerProductSpace
open NAPPAL.VPEB

namespace TiltedCvx

/-- **Theorem 34 (approximate mean values for lsc functions).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 34, p.51. Let `f : ℝ^d → ℝ̄` be proper lsc, `x ≠ y` in `dom(f)`, and
`z_λ = λx + (1 − λ)y`. Then there is `λ ∈ [0, 1)` with `z_λ ∈ dom(f)` and sequences
`x_k →^f z_λ`, `v_k ∈ ∂̂f(x_k)` with `(1/(1 − λ)) limsup ⟨v_k, x_k − x⟩ ≤ f(y) − f(x)` and
`limsup ⟨v_k, y − x⟩ ≤ f(y) − f(x)`. Similarly there is `λ′ ∈ (0, 1]` with `z_λ′ ∈ dom(f)` and
`x′_k →^f z_λ′`, `v′_k ∈ ∂̂f(x′_k)` with `f(y) − f(x) ≤ (1/λ′) liminf ⟨v′_k, y − x′_k⟩` and
`f(y) − f(x) ≤ liminf ⟨v′_k, y − x⟩`.

**Formalization Note** `ℝ^d` is a finite-dimensional real inner product space `E`; `∂̂f` is the
published `NAPPAL.VPEB.frechetSubdiff`.
`x_k →^f z` (f-attentive convergence, p.11) is `x_k → z` together with `f(x_k) → f(z)` in
`EReal`. The upper and lower limits are taken in `EReal` of the real inner products, so they
exist without any boundedness; the positive factors `1/(1 − λ)`, `1/λ′` multiply them in `EReal`.
`f(y) − f(x)` is the real number `(f y).toReal − (f x).toReal`. -/
theorem theorem_34 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) (hf : IsProper f) (hlsc : LowerSemicontinuous f)
    (x y : E) (hx : x ∈ effDom f) (hy : y ∈ effDom f) (hxy : x ≠ y) :
    (∃ l : ℝ, 0 ≤ l ∧ l < 1 ∧ l • x + (1 - l) • y ∈ effDom f ∧
      ∃ xs vs : ℕ → E,
        Tendsto xs atTop (𝓝 (l • x + (1 - l) • y)) ∧
        Tendsto (fun k => f (xs k)) atTop (𝓝 (f (l • x + (1 - l) • y))) ∧
        (∀ k, vs k ∈ frechetSubdiff f (xs k)) ∧
        (((1 - l)⁻¹ : ℝ) : EReal) *
            limsup (fun k => ((⟪vs k, xs k - x⟫_ℝ : ℝ) : EReal)) atTop ≤
          (((f y).toReal - (f x).toReal : ℝ) : EReal) ∧
        limsup (fun k => ((⟪vs k, y - x⟫_ℝ : ℝ) : EReal)) atTop ≤
          (((f y).toReal - (f x).toReal : ℝ) : EReal)) ∧
    (∃ l' : ℝ, 0 < l' ∧ l' ≤ 1 ∧ l' • x + (1 - l') • y ∈ effDom f ∧
      ∃ xs' vs' : ℕ → E,
        Tendsto xs' atTop (𝓝 (l' • x + (1 - l') • y)) ∧
        Tendsto (fun k => f (xs' k)) atTop (𝓝 (f (l' • x + (1 - l') • y))) ∧
        (∀ k, vs' k ∈ frechetSubdiff f (xs' k)) ∧
        (((f y).toReal - (f x).toReal : ℝ) : EReal) ≤
          ((l'⁻¹ : ℝ) : EReal) *
            liminf (fun k => ((⟪vs' k, y - xs' k⟫_ℝ : ℝ) : EReal)) atTop ∧
        (((f y).toReal - (f x).toReal : ℝ) : EReal) ≤
          liminf (fun k => ((⟪vs' k, y - x⟫_ℝ : ℝ) : EReal)) atTop) := by sorry

end TiltedCvx
