-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_11
-- name    : TiltedCvx.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:30:58.131167+00:00
-- url     : https://prove2.me/theorems/2088a9d8-0fc7-42b0-af3a-9858fad4bb6e
-- title:
--   Theorem 11 — limits of γ–tilted convex functions
-- statement:
--   Let $K\subseteq\mathbb R^d$ be a non-empty convex set and $\gamma\in(0,1]$. Let $f_n:\mathbb R^d\to\overline{\mathbb R}$ be proper, lower semicontinuous, $\gamma$–tilted convex functions that converge pointwise to finite values on a dense subset $D\subseteq K$. Then there is a continuous function $f:\operatorname{ri}(K)\to\mathbb R$ such that
--
--   1. $f_n\to f$ uniformly on compact subsets of $\operatorname{ri}(K)$;
--   2. the function $\operatorname{lsc}(f):\mathbb R^d\to\overline{\mathbb R}$ is $\gamma$–tilted convex.
--
--   Moreover, if there is a lower semicontinuous function $g:K\to\overline{\mathbb R}$ with $f_n\to g$ pointwise, then
--
--   $$
--   \operatorname{lsc}(g)=\operatorname{lsc}(f),
--   $$
--
--   and so it is $\gamma$–tilted convex.
--
--   This extends the classical stability of convex functions under pointwise limits to the class $\mathcal F^\gamma$.
--
--   **Formalization Note** The members of $\mathcal F^\gamma$ are elements of the published `classF γ`. The envelopes are `lscEnv (ri K) f` and `lscEnv K g`; lower semicontinuity of $g$ on $K$ is `LowerSemicontinuousOn g K`, and the convergence $f_n\to g$ is pointwise on $K$ in $\overline{\mathbb R}$.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: D is a dense subset of K → D ⊆ K ⊆ closure D; reason: the meaning of density in K
--   - encoding: a continuous f : ri(K) → ℝ → f : E → ℝ with ContinuousOn f (ri K), read only on ri K; reason: values off ri(K) never enter (lscEnv (ri K) and the uniform bounds read only ri K)
--   - encoding: fₙ → f uniformly on compact subsets of ri(K) → for every compact C ⊆ ri K and ε > 0, eventually f x − ε ≤ fₙ x ≤ f x + ε on C (in EReal); reason: uniform convergence of ℝ̄-valued fₙ to a real f; it forces fₙ to be finite on C eventually, as |fₙ − f| ≤ ε requires
--   - reading: lsc(f) is γ–tilted convex (and so is lsc(g)) → lsc(f) ∈ classF γ and lsc(g) ∈ classF γ: proper, lsc and γ–tilted convex; reason: Definition 3 defines γ–tilted convexity for proper lsc functions; the envelope is lsc and is proper here, so the statement inside the definition's scope is the non-weaker reading
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 11, p.21

import Mathlib
import Definitions.Def_TiltedCvx_classF
import Definitions.Def_TiltedCvx_Supplement_lscEnv

open Filter Topology

namespace TiltedCvx.Supplement

/-- **Theorem 11 (limits of γ–tilted convex functions).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 11, p.21. Let `K ⊆ ℝ^d` be a non-empty convex set and `γ ∈ (0, 1]`.
Let `fₙ : ℝ^d → ℝ̄` be proper, lsc, and γ–tilted convex functions that converge pointwise to
finite values on a dense subset `D ⊆ K`. Then there is a continuous function `f : ri(K) → ℝ` such
that (i) `fₙ → f` uniformly on compact subsets of `ri(K)`; (ii) the function `lsc(f) : ℝ^d → ℝ̄` is
γ–tilted convex. Moreover, if there is an lsc function `g : K → ℝ̄` such that `fₙ → g` pointwise,
then `lsc(g) = lsc(f)` and so it is γ–tilted convex.

**Formalization Note** "Proper, lsc, and γ–tilted convex" is membership in the published
`classF γ`; the conclusions "is γ–tilted convex" are stated as membership in `classF γ`, since
Definition 3 applies to proper lsc functions. "`D` dense in `K`" is `D ⊆ K ⊆ closure D`.
`f : ri(K) → ℝ` is a real function on `E` read only on `ri(K) = intrinsicInterior ℝ K`.
Uniform convergence on a compact `C ⊆ ri(K)`: for every `ε > 0`, eventually
`f x − ε ≤ fₙ x ≤ f x + ε` for all `x ∈ C` (so `fₙ` is eventually finite on `C`).
`lsc(f)` is `lscEnv (ri K) f` (the envelope of `f` extended by `+∞` off `ri(K)`), and `lsc(g)` for
`g : K → ℝ̄` is `lscEnv K g`; lower semicontinuity of `g` as a function on `K` is
`LowerSemicontinuousOn g K`, and the pointwise convergence `fₙ → g` is on `K`, in `EReal`. -/
theorem theorem_11 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hKne : K.Nonempty) (hKc : Convex ℝ K)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (fn : ℕ → E → EReal)
    (hfn : ∀ n, fn n ∈ (TiltedCvx.classF γ : Set (E → EReal)))
    (D : Set E) (hDK : D ⊆ K) (hKD : K ⊆ closure D)
    (hconv : ∀ x ∈ D, ∃ L : ℝ, Tendsto (fun n => fn n x) atTop (𝓝 (L : EReal))) :
    ∃ f : E → ℝ, ContinuousOn f (intrinsicInterior ℝ K) ∧
      (∀ C ⊆ intrinsicInterior ℝ K, IsCompact C → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ x ∈ C,
          (((f x - ε : ℝ) : EReal) ≤ fn n x ∧ fn n x ≤ ((f x + ε : ℝ) : EReal))) ∧
      lscEnv (intrinsicInterior ℝ K) (fun x => ((f x : ℝ) : EReal)) ∈
        (TiltedCvx.classF γ : Set (E → EReal)) ∧
      (∀ g : E → EReal, LowerSemicontinuousOn g K →
        (∀ x ∈ K, Tendsto (fun n => fn n x) atTop (𝓝 (g x))) →
        lscEnv K g = lscEnv (intrinsicInterior ℝ K) (fun x => ((f x : ℝ) : EReal)) ∧
        lscEnv K g ∈ (TiltedCvx.classF γ : Set (E → EReal))) := by sorry

end TiltedCvx.Supplement
