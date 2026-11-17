-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_17
-- name    : TiltedCvx.Supplement.theorem_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:32:33.067563+00:00
-- url     : https://prove2.me/theorems/cd2877ed-70d6-4737-abe7-5733748dd9d5
-- title:
--   Theorem 17 — stability of γ–tilted monotone subdifferentials
-- statement:
--   Let $K\subseteq\mathbb R^d$ be a nonempty convex set and $\gamma\in(0,1]$. Let $f_n:\mathbb R^d\to\overline{\mathbb R}$ be proper lower semicontinuous functions such that $\overline\partial f_n$ is $\gamma$–tilted monotone for every $n$, and suppose that $f_n$ converges pointwise to finite values on a dense subset $D\subseteq K$. Then there is a continuous function $f:\operatorname{ri}(K)\to\mathbb R$ such that
--
--   1. $f_n\to f$ uniformly on compact subsets of $\operatorname{ri}(K)$;
--   2. with $\bar f:=\operatorname{lsc}(f)$, the operator $\overline\partial\bar f$ is $\gamma$–tilted monotone.
--
--   Moreover, if there is a lower semicontinuous $g:K\to\overline{\mathbb R}$ with $f_n\to g$ pointwise on $K$, then $\operatorname{lsc}(g)=\bar f$, and hence $\overline\partial(\operatorname{lsc}(g))$ is $\gamma$–tilted monotone.
--
--   The class $\mathcal F^\gamma_{\mathrm{mono}}$ is thus stable under limits in the same sense as $\mathcal F^\gamma$ (Theorem 11).
--
--   **Formalization Note** "Proper lsc with $\overline\partial f_n$ $\gamma$–tilted monotone" is membership in the published `classMono γ`. Conventions for the envelopes and the convergence are those of Theorem 11.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: D is a dense subset of K → D ⊆ K ⊆ closure D; reason: the meaning of density in K
--   - encoding: a continuous f : ri(K) → ℝ → f : E → ℝ with ContinuousOn f (ri K), read only on ri K; reason: values off ri(K) never enter (lscEnv (ri K) and the uniform bounds read only ri K)
--   - encoding: fₙ → f uniformly on compact subsets of ri(K) → for every compact C ⊆ ri K and ε > 0, eventually f x − ε ≤ fₙ x ≤ f x + ε on C (in EReal); reason: uniform convergence of ℝ̄-valued fₙ to a real f; it forces fₙ to be finite on C eventually, as |fₙ − f| ≤ ε requires
--   - reading: ∂̄f̄ is γ–tilted monotone (and so is ∂̄(lsc g)) → f̄ ∈ classMono γ and lsc(g) ∈ classMono γ: proper, lsc, with γ–tilted monotone ∂̄; reason: the Clarke subdifferential of Definition 2 is defined for proper locally lsc functions; the envelope is lsc and proper here, so this is the non-weaker reading
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 17, p.24

import Mathlib
import Definitions.Def_TiltedCvx_classMono
import Definitions.Def_TiltedCvx_Supplement_lscEnv

open Filter Topology

namespace TiltedCvx.Supplement

/-- **Theorem 17 (stability of γ–tilted monotone subdifferentials).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 17, p.24. Let `K ⊆ ℝ^d` be a nonempty
convex set and `γ ∈ (0, 1]`. Let `fₙ : ℝ^d → ℝ̄` be proper lsc functions such that `∂̄fₙ` is
γ–tilted monotone for every `n`. Suppose that `fₙ` converges pointwise to finite values on a dense
subset `D ⊆ K`. Then there is a continuous function `f : ri(K) → ℝ` such that (i) `fₙ → f`
uniformly on compact subsets of `ri(K)`; (ii) if `f̄ := lsc(f)`, then `∂̄f̄` is γ–tilted monotone.
Moreover, if there is an lsc function `g : K → ℝ̄` such that `fₙ → g` pointwise on `K`, then
`lsc(g) = f̄`, and hence `∂̄(lsc(g))` is γ–tilted monotone.

**Formalization Note** "Proper lsc with `∂̄fₙ` γ–tilted monotone" is membership in the published
`classMono γ`; the conclusions "`∂̄f̄` is γ–tilted monotone" are stated as `f̄ ∈ classMono γ`
(proper, lsc, `∂̄f̄` γ–tilted monotone), since the Clarke subdifferential of Definition 2 is taken
for proper locally lsc functions. The other conventions are those of `theorem_11`: `D ⊆ K ⊆
closure D`; uniform convergence on compacts `C ⊆ ri(K)` as eventual two-sided `ε`-bounds;
`f̄ = lscEnv (ri K) f`, `lsc(g) = lscEnv K g`, `g` lsc on `K`. -/
theorem theorem_17 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hKne : K.Nonempty) (hKc : Convex ℝ K)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (fn : ℕ → E → EReal)
    (hfn : ∀ n, fn n ∈ (TiltedCvx.classMono γ : Set (E → EReal)))
    (D : Set E) (hDK : D ⊆ K) (hKD : K ⊆ closure D)
    (hconv : ∀ x ∈ D, ∃ L : ℝ, Tendsto (fun n => fn n x) atTop (𝓝 (L : EReal))) :
    ∃ f : E → ℝ, ContinuousOn f (intrinsicInterior ℝ K) ∧
      (∀ C ⊆ intrinsicInterior ℝ K, IsCompact C → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ x ∈ C,
          (((f x - ε : ℝ) : EReal) ≤ fn n x ∧ fn n x ≤ ((f x + ε : ℝ) : EReal))) ∧
      lscEnv (intrinsicInterior ℝ K) (fun x => ((f x : ℝ) : EReal)) ∈
        (TiltedCvx.classMono γ : Set (E → EReal)) ∧
      (∀ g : E → EReal, LowerSemicontinuousOn g K →
        (∀ x ∈ K, Tendsto (fun n => fn n x) atTop (𝓝 (g x))) →
        lscEnv K g = lscEnv (intrinsicInterior ℝ K) (fun x => ((f x : ℝ) : EReal)) ∧
        lscEnv K g ∈ (TiltedCvx.classMono γ : Set (E → EReal))) := by sorry

end TiltedCvx.Supplement
