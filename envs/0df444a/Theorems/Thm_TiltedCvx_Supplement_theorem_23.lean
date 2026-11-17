-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_23
-- name    : TiltedCvx.Supplement.theorem_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:34:16.599815+00:00
-- url     : https://prove2.me/theorems/786e8d53-4789-4cb7-a0f3-ae7296c962d6
-- title:
--   Theorem 23 — stability of γ–tilted secant convexity under limits
-- statement:
--   Let $K\subseteq\mathbb R^d$ be a non-empty convex set and $\gamma\in(0,1]$. Let $f_n:\mathbb R^d\to\overline{\mathbb R}$ be proper $\gamma$–tilted secant convex functions that converge pointwise to finite values on a dense subset $D\subseteq K$. Then there is a continuous function $f:\operatorname{ri}(K)\to\mathbb R$ such that
--
--   1. $f_n\to f$ uniformly on compact subsets of $\operatorname{ri}(K)$;
--   2. $f$ is $\gamma$–tilted secant convex.
--
--   Moreover, if there is a function $g:K\to\overline{\mathbb R}$ with $f_n\to g$ pointwise on $K$, then $g$ never takes the value $-\infty$ and is $\gamma$–tilted secant convex.
--
--   No lower semicontinuity is assumed.
--
--   **Formalization Note** The secant convexity of $f:\operatorname{ri}(K)\to\mathbb R$ and of $g:K\to\overline{\mathbb R}$ is that of their proper extensions (`properExt (ri K) f`, and $g$ on $K$, $+\infty$ off $K$).
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: D is a dense subset of K → D ⊆ K ⊆ closure D; reason: the meaning of density in K
--   - encoding: fₙ → f uniformly on compact subsets of ri(K) → for every compact C ⊆ ri K and ε > 0, eventually f x − ε ≤ fₙ x ≤ f x + ε on C (in EReal); reason: uniform convergence of ℝ̄-valued fₙ to a real f; it forces fₙ to be finite on C eventually, as |fₙ − f| ≤ ε requires
--   - encoding: a continuous f : ri(K) → ℝ, and g : K → ℝ̄ → f : E → ℝ continuous on ri K, its secant convexity that of properExt (ri K) f; g : E → EReal read on K, extended by ⊤ off K; reason: the paper's convention that class membership refers to the proper extension (§3)
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 23, p.28

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedSecant
import Definitions.Def_TiltedCvx_properExt

open Filter Topology Classical

namespace TiltedCvx.Supplement

/-- **Theorem 23 (stability of γ–tilted secant convexity under limits).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 23, p.28. Let `K ⊆ ℝ^d` be a non-empty
convex set and `γ ∈ (0, 1]`. Let `fₙ : ℝ^d → ℝ̄` be proper γ–tilted secant convex functions that
converge pointwise to finite values on a dense subset `D ⊆ K`. Then there is a continuous function
`f : ri(K) → ℝ` such that (i) `fₙ → f` uniformly on compact subsets of `ri(K)`; (ii) `f` is
γ–tilted secant convex. Moreover, if there is a function `g : K → ℝ̄` such that `fₙ → g` pointwise
on `K`, then `g` never takes the value `−∞` and is γ–tilted secant convex.

**Formalization Note** No lower semicontinuity is assumed. "`D` dense in `K`" is
`D ⊆ K ⊆ closure D`. `f : ri(K) → ℝ` is a real function on `E` read on `ri(K)`, and its secant
convexity is that of its proper extension (`properExt (ri K) f`). Uniform convergence on a compact
`C ⊆ ri(K)`: for every `ε > 0`, eventually `f x − ε ≤ fₙ x ≤ f x + ε` on `C`. `g : K → ℝ̄` is a
function on `E` read on `K`; its secant convexity is that of `g` on `K`, `+∞` off `K`. -/
theorem theorem_23 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hKne : K.Nonempty) (hKc : Convex ℝ K)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (fn : ℕ → E → EReal)
    (hfn : ∀ n, TiltedCvx.IsProper (fn n) ∧ TiltedCvx.TiltedSecant γ (fn n))
    (D : Set E) (hDK : D ⊆ K) (hKD : K ⊆ closure D)
    (hconv : ∀ x ∈ D, ∃ L : ℝ, Tendsto (fun n => fn n x) atTop (𝓝 (L : EReal))) :
    ∃ f : E → ℝ, ContinuousOn f (intrinsicInterior ℝ K) ∧
      (∀ C ⊆ intrinsicInterior ℝ K, IsCompact C → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ x ∈ C,
          (((f x - ε : ℝ) : EReal) ≤ fn n x ∧ fn n x ≤ ((f x + ε : ℝ) : EReal))) ∧
      TiltedCvx.TiltedSecant γ (TiltedCvx.properExt (intrinsicInterior ℝ K) f) ∧
      (∀ g : E → EReal, (∀ x ∈ K, Tendsto (fun n => fn n x) atTop (𝓝 (g x))) →
        (∀ x ∈ K, g x ≠ ⊥) ∧
        TiltedCvx.TiltedSecant γ (fun x => if x ∈ K then g x else ⊤)) := by sorry

end TiltedCvx.Supplement
