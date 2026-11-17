-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_19
-- name    : TiltedCvx.Supplement.theorem_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:33:46.230293+00:00
-- url     : https://prove2.me/theorems/a4ebacd7-e149-46d9-bebd-8d24a411b73e
-- title:
--   Theorem 19 — basic properties of γ–tilted secant convexity
-- statement:
--   Let $\gamma\in[0,1]$, $X\subseteq\mathbb R^d$ convex, and $f:X\to\mathbb R\cup\{+\infty\}$ with $K:=\operatorname{dom}(f)$. Then:
--
--   1. if $f$ is $\gamma$–tilted secant convex, then it is quasiconvex and $K$ is convex;
--   2. if $f$ is convex, then it is $\gamma$–tilted secant convex;
--   3. the set of $\gamma$–tilted secant convex functions over $X$ is closed under arbitrary non-empty suprema;
--   4. if $f$ is $\gamma$–tilted secant convex and $C\subseteq X$ is convex, then $f|_C:C\to\mathbb R\cup\{+\infty\}$ is $\gamma$–tilted secant convex;
--   5. if $\gamma\in(0,1]$ and $f$ is $\gamma$–tilted secant convex, then $\operatorname{lsc}(f):\mathbb R^d\to\mathbb R\cup\{+\infty\}$ is $\gamma$–tilted secant convex and $f=\operatorname{lsc}(f)$ on $\operatorname{ri}(K)$;
--   6. $f$ is $\gamma$–tilted secant convex if and only if, for every line $\ell$ meeting $X$, the restriction $f|_\ell:\ell\cap X\to\mathbb R\cup\{+\infty\}$ is $\gamma$–tilted secant convex.
--
--   These are the analogues for $\mathcal F^\gamma_{\mathrm{sec}}$ of the elementary closure properties of convex functions.
--
--   **Formalization Note** A function $X\to\mathbb R\cup\{+\infty\}$ is encoded by its proper extension: $f:E\to\overline{\mathbb R}$, never $-\infty$, equal to $+\infty$ off $X$. In item 3 the family is a non-empty set $U$ of such functions and the supremum is pointwise. A line is $\{p+te\}$ with $\|e\|=1$, regarded as $\mathbb R$ through $t\mapsto p+te$ (the published `lineRestrict`).
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: f : X → ℝ ∪ {+∞}, and the functions “over X” of (iii) → f : E → EReal, never ⊥, equal to ⊤ off X; the family is a non-empty set U of such functions and its supremum is sSup U (pointwise); reason: the paper's proper-extension convention (§3); a set-indexed family is an arbitrary family
--   - encoding: f is quasiconvex (on X) → QuasiconvexOn ℝ X f; reason: convex sublevel sets of f on X
--   - encoding: f : ℝ^d → ℝ̄ is convex → the published epigraph convexity WassersteinDRO.ConvexLossP1.IsConvexExt f (the epigraph {(x, t) : f x ≤ t} is convex); reason: the standard notion for extended-valued functions; Mathlib's ConvexOn needs an ordered-module codomain, which EReal is not
--   - encoding: f|C : C → ℝ ∪ {+∞} → x ↦ f x on C, ⊤ off C; reason: proper extension of the restriction
--   - encoding: lsc(f) : ℝ^d → ℝ ∪ {+∞} → lscEnv X f, with lscEnv X f x ≠ ⊥ for every x; reason: the codomain claim is that lsc(f) never takes −∞
--   - encoding: f|ℓ : ℓ ∩ X → ℝ ∪ {+∞} for a line ℓ meeting X → lineRestrict f p e {t | p + t • e ∈ X} with ‖e‖ = 1; reason: the unit-speed parametrization is an isometry of ℝ onto ℓ, as in the published Theorems 9 and 16
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 19, pp.25–26

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_TiltedSecant
import Definitions.Def_TiltedCvx_lineRestrict
import Definitions.Def_WassersteinDRO_ConvexLossP1_IsConvexExt
import Definitions.Def_TiltedCvx_Supplement_lscEnv

open Classical

namespace TiltedCvx.Supplement

/-- **Theorem 19 (basic properties of γ–tilted secant convexity).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 19, pp.25–26. Let `γ ∈ [0, 1]`,
`X ⊆ ℝ^d` a convex set, and `f : X → ℝ ∪ {+∞}` with effective domain `K := dom(f)`. Then:
(i) if `f` is γ–tilted secant convex, then it is quasiconvex, and `K` is convex;
(ii) if `f` is convex, then it is γ–tilted secant convex;
(iii) the set of γ–tilted secant convex functions over `X` is closed under arbitrary non-empty
suprema;
(iv) if `f` is γ–tilted secant convex and `C ⊆ X` is convex, then `f|C : C → ℝ ∪ {+∞}` is
γ–tilted secant convex;
(v) if `γ ∈ (0, 1]` and `f` is γ–tilted secant convex, then `lsc(f) : ℝ^d → ℝ ∪ {+∞}` is γ–tilted
secant convex and `f = lsc(f)` on `ri(K)`;
(vi) `f` is γ–tilted secant convex if and only if, for every line `ℓ` that intersects `X`, the
restriction `f|ℓ : ℓ ∩ X → ℝ ∪ {+∞}` is γ–tilted secant convex.

**Formalization Note** A function `X → ℝ ∪ {+∞}` is encoded by its proper extension: `f : E →
EReal`, never `−∞`, equal to `+∞` off `X`; the functions "over `X`" in (iii) are those of this form,
and their supremum is the pointwise supremum `sSup U`. Quasiconvexity of `f` on `X` is
`QuasiconvexOn ℝ X f`; convexity of `f` is the published epigraph convexity `IsConvexExt`. `f|C` is
`f` on `C` and `+∞` elsewhere. `lsc(f)` is `lscEnv X f`, and "`lsc(f)` maps into `ℝ ∪ {+∞}`" is
stated as `lsc(f) ≠ −∞` everywhere. A line is `{p + t e : t ∈ ℝ}` with `‖e‖ = 1`, identified with `ℝ`
by its unit-speed parametrization; `f|ℓ` on `ℓ ∩ X` is the published `lineRestrict f p e I` with `I`
the parameters of `ℓ ∩ X` (`+∞` off `I`). -/
theorem theorem_19 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (X : Set E)
    (hX : Convex ℝ X) (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (htop : ∀ x ∉ X, f x = ⊤) :
    (TiltedCvx.TiltedSecant γ f →
      QuasiconvexOn ℝ X f ∧ Convex ℝ (TiltedCvx.effDom f)) ∧
    (WassersteinDRO.ConvexLossP1.IsConvexExt f → TiltedCvx.TiltedSecant γ f) ∧
    (∀ U : Set (E → EReal), U.Nonempty →
      (∀ g ∈ U, (∀ x, g x ≠ ⊥) ∧ (∀ x ∉ X, g x = ⊤) ∧ TiltedCvx.TiltedSecant γ g) →
        (∀ x, sSup U x ≠ ⊥) ∧ (∀ x ∉ X, sSup U x = ⊤) ∧ TiltedCvx.TiltedSecant γ (sSup U)) ∧
    (∀ C : Set E, C ⊆ X → Convex ℝ C → TiltedCvx.TiltedSecant γ f →
      TiltedCvx.TiltedSecant γ (fun x => if x ∈ C then f x else ⊤)) ∧
    (0 < γ → TiltedCvx.TiltedSecant γ f →
      (∀ x, lscEnv X f x ≠ ⊥) ∧ TiltedCvx.TiltedSecant γ (lscEnv X f) ∧
      ∀ x ∈ intrinsicInterior ℝ (TiltedCvx.effDom f), f x = lscEnv X f x) ∧
    (TiltedCvx.TiltedSecant γ f ↔
      ∀ p e : E, ‖e‖ = 1 → (∃ t : ℝ, p + t • e ∈ X) →
        TiltedCvx.TiltedSecant γ (TiltedCvx.lineRestrict f p e {t | p + t • e ∈ X})) := by sorry

end TiltedCvx.Supplement
