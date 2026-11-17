-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_26
-- name    : TiltedCvx.Supplement.theorem_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:36:36.873226+00:00
-- url     : https://prove2.me/theorems/be2f0197-855b-40ce-a2c5-b3080e30898b
-- title:
--   Theorem 26 — comparison vector with coefficient γ
-- statement:
--   Let $\gamma\in(0,1]$, $K\subseteq\mathbb R^d$ convex, $f:K\to\mathbb R$ continuous with $f\in\mathcal F^\gamma$, $x\in K$, and $q=q_f(x)$ a support vector at $x$. The set
--
--   $$
--   \big\{v\in[\gamma q,\gamma^{-1}q]\ :\ f(x)-\overline\psi_\gamma(f(y))\le\langle v,x-y\rangle\ \text{for every }y\in K\big\}\qquad\text{(43)}
--   $$
--
--   is nonempty, convex and compact. Let $g(f,x)$ be its element of minimum norm. Then
--
--   $$
--   f(x)-\overline\psi_\gamma(f(y))\le\langle g(f,x),x-y\rangle\quad(y\in K),\qquad\|g(f,x)\|\le\|\gamma^{-1}q_f(x)\|.\qquad\text{(44)}
--   $$
--
--   In particular, continuous functions on $K$ in $\mathcal F^\gamma$ form a lower-linearizable class with coefficient $\gamma$, and $\|g(f,x)\|\le\gamma^{-1}G$ under the oracle bound $\|q_f(z)\|\le G$ of Section 7.
--
--   This is the comparison vector that reduces online $\gamma$–tilted convex optimization to online linear optimization with $\gamma$–regret.
--
--   Here $\overline\psi_\gamma(z)=\max\{\gamma z,\gamma^{-1}z\}$ is the upper tilt (published `TiltedCvx.psiBar`), while a support vector satisfies inequality (4) with the lower tilt $\psi_\gamma$.
--
--   **Formalization Note** $f\in\mathcal F^\gamma$ means that the proper extension of $f$ lies in the published `classF γ`. The first part asserts that an element of minimum norm exists and that every such element satisfies (44). In the second part the class consists of the continuous members of $\mathcal F^\gamma$ that have a support vector at every point of $K$, and for every choice $q_f(x)$ of support vectors there is a map $g$ satisfying (41) with $\alpha=\gamma$ and the norm bounds.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - reading: γ (the coefficient of §8) → γ ∈ (0, 1]; reason: the statement uses γ⁻¹ and F^γ is defined for γ ∈ [0, 1]; γ = 0 is excluded
--   - encoding: f : K → ℝ continuous with f ∈ F^γ → f : E → ℝ, ContinuousOn f K, properExt K f ∈ classF γ; reason: the paper's convention that class membership refers to the proper extension (§3)
--   - reading: q_f(x) is a support vector at x (§8.3's standing assumption), and in the “in particular” clause the oracle q_f of §7 → hypothesis IsSupportVector γ K f x q; the class of the “in particular” clause is the continuous members of F^γ with a support vector at every point of K; reason: without a support vector the class claim fails: f = −√x on K = [0, 1] is in F¹ ⊆ F^γ, has no support vector at 0, and (41) at x = 0 would need g ≤ −γ/√y for every y ∈ (0, 1]
--   - encoding: g(f, x) := the element of minimum norm → an element of minimum norm exists, and every element of minimum norm satisfies (44); reason: covers the paper's g(f, x) without presupposing uniqueness
--   - reading: lower-linearizable class with coefficient γ ((40)) → a map g satisfying (41) (χ = id, β = 1) together with ‖g(f, x)‖ ≤ γ⁻¹‖q_f(x)‖ and ‖g(f, x)‖ ≤ γ⁻¹G when ‖q_f(z)‖ ≤ G on K; reason: the paper's results use only χ = id, β = 1 (p.41), which implies (40)
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 26, p.42 (standing assumptions of §8.3, p.41; oracle (33) and bound, §7, p.37)

import Mathlib
import Definitions.Def_TiltedCvx_psi
import Definitions.Def_TiltedCvx_psiBar
import Definitions.Def_TiltedCvx_classF
import Definitions.Def_TiltedCvx_properExt
import Definitions.Def_TiltedCvx_Supplement_IsSupportVector
import Definitions.Def_TiltedCvx_Supplement_comparisonSet
import Definitions.Def_TiltedCvx_Supplement_IsComparisonMap

open scoped InnerProductSpace

namespace TiltedCvx.Supplement

/-- **Theorem 26 (comparison vector with coefficient γ).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 26, p.42 (with the standing assumptions of §8.3, p.41). Let `K` be a
convex set, `f : K → ℝ` continuous with `f ∈ F^γ`, `x ∈ K`, and `q_f(x)` a support vector at `x`.
The set `{v ∈ [γq_f(x), γ⁻¹q_f(x)] : f(x) − ψ̄γ(f(y)) ≤ ⟨v, x − y⟩ for every y ∈ K}` (43) is
nonempty, convex, and compact. Let `g(f, x)` be its element of minimum norm. Then
`f(x) − ψ̄γ(f(y)) ≤ ⟨g(f, x), x − y⟩` (`y ∈ K`) and `‖g(f, x)‖ ≤ ‖γ⁻¹q_f(x)‖` (44). In particular,
continuous functions on `K` in `F^γ` form a lower-linearizable class with coefficient `γ`, and
`‖g(f, x)‖ ≤ γ⁻¹G` under the oracle bound of Section 7.

**Formalization Note** `γ ∈ (0, 1]`. The tilt in (43)–(44) and (41) is the upper tilt
`ψ̄γ(z) = max{γz, γ⁻¹z}` (published `TiltedCvx.psiBar`; the bar is on the rendered page and lost in
the text layer), while the support vector uses `ψγ` of (4). `f ∈ F^γ` for `f : K → ℝ` is membership of its proper
extension `properExt K f` in the published `classF γ`; continuity is `ContinuousOn f K`. "`q` is a
support vector at `x`" is §8.3's standing assumption (inequality (4) at `x` with `v = q`, for every
`y ∈ K`, as returned by the oracle (33) of §7), carried as a hypothesis. The first conjunct gives
the existence of an element of minimum norm and (44) for every such element. In the "in
particular" clause the class is the continuous members of `F^γ` on `K` that have a support vector
at every point of `K` (the access model of §7, under which `q_f(x)` exists); for every choice of
support vectors `q f x` there is a map `g` satisfying (41) with `α = γ` (lower-linearizability with
`χ = id`, `β = 1`) and `‖g(f, x)‖ ≤ γ⁻¹‖q_f(x)‖`, hence `‖g(f, x)‖ ≤ γ⁻¹G` whenever `‖q_f(z)‖ ≤ G`
on `K` (the oracle bound of §7). -/
theorem theorem_26 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (K : Set E)
    (hK : Convex ℝ K) :
    (∀ f : E → ℝ, ContinuousOn f K →
      TiltedCvx.properExt K f ∈ (TiltedCvx.classF γ : Set (E → EReal)) →
      ∀ x ∈ K, ∀ q : E, IsSupportVector γ K f x q →
        (comparisonSet γ K f x q).Nonempty ∧ Convex ℝ (comparisonSet γ K f x q) ∧
        IsCompact (comparisonSet γ K f x q) ∧
        (∃ g ∈ comparisonSet γ K f x q, ∀ v ∈ comparisonSet γ K f x q, ‖g‖ ≤ ‖v‖) ∧
        ∀ g ∈ comparisonSet γ K f x q, (∀ v ∈ comparisonSet γ K f x q, ‖g‖ ≤ ‖v‖) →
          (∀ y ∈ K, (f x : EReal) - TiltedCvx.psiBar γ (f y : EReal) ≤
            ((⟪g, x - y⟫_ℝ : ℝ) : EReal)) ∧
          ‖g‖ ≤ ‖γ⁻¹ • q‖) ∧
    ((∃ g : (E → ℝ) → E → E, IsComparisonMap γ K
        {f | ContinuousOn f K ∧ TiltedCvx.properExt K f ∈ (TiltedCvx.classF γ : Set (E → EReal)) ∧
          ∀ x ∈ K, ∃ q : E, IsSupportVector γ K f x q} g) ∧
      ∀ q : (E → ℝ) → E → E,
        (∀ f : E → ℝ, ContinuousOn f K →
          TiltedCvx.properExt K f ∈ (TiltedCvx.classF γ : Set (E → EReal)) →
          (∀ x ∈ K, ∃ q' : E, IsSupportVector γ K f x q') →
          ∀ x ∈ K, IsSupportVector γ K f x (q f x)) →
        ∃ g : (E → ℝ) → E → E,
          IsComparisonMap γ K
            {f | ContinuousOn f K ∧
              TiltedCvx.properExt K f ∈ (TiltedCvx.classF γ : Set (E → EReal)) ∧
              ∀ x ∈ K, ∃ q' : E, IsSupportVector γ K f x q'} g ∧
          ∀ f : E → ℝ, ContinuousOn f K →
            TiltedCvx.properExt K f ∈ (TiltedCvx.classF γ : Set (E → EReal)) →
            (∀ x ∈ K, ∃ q' : E, IsSupportVector γ K f x q') →
            ∀ x ∈ K, ‖g f x‖ ≤ γ⁻¹ * ‖q f x‖ ∧
              ∀ G : ℝ, (∀ z ∈ K, ‖q f z‖ ≤ G) → ‖g f x‖ ≤ γ⁻¹ * G) := by sorry

end TiltedCvx.Supplement
