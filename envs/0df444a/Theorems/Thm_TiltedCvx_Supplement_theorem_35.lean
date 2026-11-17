-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_35
-- name    : TiltedCvx.Supplement.theorem_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:37:07.745945+00:00
-- url     : https://prove2.me/theorems/109ea1af-2233-468d-bac0-035f68111fc0
-- title:
--   Theorem 35 — local Lipschitz regularity from approximate γ–tilted convexity
-- statement:
--   Let $\gamma\in(0,1]$, $f:\mathbb R^d\to\overline{\mathbb R}$ proper and lower semicontinuous, $K:=\operatorname{dom}(f)$ convex, and $F:\mathbb R^d\rightrightarrows\mathbb R^d$ such that $K\cap\operatorname{dom}(F)$ is dense in $K$ and $f$ is approximately $\gamma$–tilted convex with respect to $F$ (Definition 16). Then $f$ is locally Lipschitz on $\operatorname{ri}(K)$. More precisely, put $A:=\operatorname{aff}(K)$. If $x_0\in\operatorname{ri}(K)$ and $R>0$ satisfy $\overline B(x_0,3R)\cap A\subseteq K$, then
--
--   $$
--   M:=\sup\{|f(x)|:x\in \overline B(x_0,2R)\cap A\}<\infty,\qquad |f(x)-f(y)|\le\frac{2M}{\gamma^2R}\|x-y\|\quad\forall x,y\in B(x_0,R)\cap A,\qquad\text{(79)}
--   $$
--
--   and, in translation-invariant form,
--
--   $$
--   |f(x)-f(y)|\le\frac{\Delta}{\gamma^2R}\|x-y\|\quad\forall x,y\in B(x_0,R)\cap A,\qquad \Delta:=\sup_{\overline B(x_0,2R)\cap A}f-\inf_{\overline B(x_0,2R)\cap A}f.\qquad\text{(80)}
--   $$
--
--   The constant depends only on a local bound for $f$ and the local geometry of its domain, which is what makes it uniform along sequences.
--
--   **Formalization Note** $B(x,r)$ is the open ball, $\overline B(x,r)$ the closed ball (the bars on the $3R$ and $2R$ balls are on the rendered page and lost in the text layer), and $A$ the affine span of $K$. On $\overline B(x_0,3R)\cap A\subseteq K$ the function is finite and is read as a real function; $M$ and $\Delta$ are real suprema and infima of nonempty bounded value sets.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: f|ri(K) is locally Lipschitz → LocallyLipschitzOn (ri K) of x ↦ (f x).toReal, ri K = intrinsicInterior ℝ K; reason: f is finite on ri(K) ⊆ dom f, so toReal reads its values; same condition
--   - encoding: K ∩ dom(F) dense in K → K ⊆ closure (K ∩ {x | F x ≠ ∅}); reason: the meaning of density in K, with dom F = {x : F(x) ≠ ∅}
--   - encoding: M < ∞, M and Δ as sup/inf of f over B̄(x₀, 2R) ∩ A → BddAbove of {|f x|}; M, Δ as real sSup/sInf of the toReal value sets; reason: f is finite on B̄(x₀, 3R) ∩ A ⊆ K, and these sets are nonempty (x₀) and, by the first clause, bounded
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 35, p.55

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_Supplement_ApproxTiltedConvexWrt

namespace TiltedCvx.Supplement

/-- **Theorem 35 (local Lipschitz regularity from approximate γ–tilted convexity).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 35, p.55. Let `γ ∈ (0, 1]`, let
`f : ℝ^d → ℝ̄` be proper and lsc, and set `K := dom(f)`. Assume that `K` is convex. Let
`F : ℝ^d ⇒ ℝ^d` be such that `K ∩ dom(F)` is dense in `K`, and suppose that `f` is approximately
γ–tilted convex with respect to `F` (Definition 16). Then `f` is locally Lipschitz on `ri(K)`.
More precisely, put `A := aff(K)`. If `x₀ ∈ ri(K)` and `R > 0` satisfy `B̄(x₀, 3R) ∩ A ⊆ K`, then
`M := sup{|f(x)| : x ∈ B̄(x₀, 2R) ∩ A} < ∞`, and
`|f(x) − f(y)| ≤ (2M/(γ²R))‖x − y‖` for all `x, y ∈ B(x₀, R) ∩ A` (79). The translation-invariant
form is `|f(x) − f(y)| ≤ (Δ/(γ²R))‖x − y‖`, `x, y ∈ B(x₀, R) ∩ A` (80), where
`Δ := sup_{B̄(x₀,2R)∩A} f − inf_{B̄(x₀,2R)∩A} f`.

**Formalization Note** `B(x, r)` is the open ball `Metric.ball x r` and `B̄(x, r)` the closed ball
`Metric.closedBall x r` (the rendered page has the bar on the `3R` and `2R` balls, which the text
layer drops; the `R` ball of (79)–(80) is open), `A` is `affineSpan ℝ K`
(as a set), `ri(K)` is `intrinsicInterior ℝ K`. "`K ∩ dom(F)` dense in `K`" is
`K ⊆ closure (K ∩ {x | F x ≠ ∅})`. On `B̄(x₀, 3R) ∩ A ⊆ K` the function is finite, so it is read
through `toReal`; `M < ∞` is `BddAbove` of `{|f(x)|}`, and `M`, `Δ` are the real `sSup`/`sInf`
of the (nonempty, bounded) value sets. "Locally Lipschitz on `ri(K)`" is `LocallyLipschitzOn`. -/
theorem theorem_35 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : TiltedCvx.IsProper f) (hlsc : LowerSemicontinuous f)
    (hK : Convex ℝ (TiltedCvx.effDom f)) (F : E → Set E)
    (hdense : TiltedCvx.effDom f ⊆ closure (TiltedCvx.effDom f ∩ {x | (F x).Nonempty}))
    (happrox : ApproxTiltedConvexWrt γ f F) :
    LocallyLipschitzOn (intrinsicInterior ℝ (TiltedCvx.effDom f)) (fun x => (f x).toReal) ∧
    ∀ x₀ ∈ intrinsicInterior ℝ (TiltedCvx.effDom f), ∀ R : ℝ, 0 < R →
      Metric.closedBall x₀ (3 * R) ∩ (affineSpan ℝ (TiltedCvx.effDom f) : Set E) ⊆
        TiltedCvx.effDom f →
      BddAbove ((fun x => |(f x).toReal|) ''
        (Metric.closedBall x₀ (2 * R) ∩ (affineSpan ℝ (TiltedCvx.effDom f) : Set E))) ∧
      (∀ x ∈ Metric.ball x₀ R ∩ (affineSpan ℝ (TiltedCvx.effDom f) : Set E),
        ∀ y ∈ Metric.ball x₀ R ∩ (affineSpan ℝ (TiltedCvx.effDom f) : Set E),
          |(f x).toReal - (f y).toReal| ≤
            2 * sSup ((fun z => |(f z).toReal|) ''
              (Metric.closedBall x₀ (2 * R) ∩ (affineSpan ℝ (TiltedCvx.effDom f) : Set E))) /
              (γ ^ 2 * R) * ‖x - y‖) ∧
      (∀ x ∈ Metric.ball x₀ R ∩ (affineSpan ℝ (TiltedCvx.effDom f) : Set E),
        ∀ y ∈ Metric.ball x₀ R ∩ (affineSpan ℝ (TiltedCvx.effDom f) : Set E),
          |(f x).toReal - (f y).toReal| ≤
            (sSup ((fun z => (f z).toReal) ''
                (Metric.closedBall x₀ (2 * R) ∩ (affineSpan ℝ (TiltedCvx.effDom f) : Set E))) -
              sInf ((fun z => (f z).toReal) ''
                (Metric.closedBall x₀ (2 * R) ∩ (affineSpan ℝ (TiltedCvx.effDom f) : Set E)))) /
              (γ ^ 2 * R) * ‖x - y‖) := by sorry

end TiltedCvx.Supplement
