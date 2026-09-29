-- Prove2me | Theorems.Thm_StochasticProg_Bounds_thm2_edmundson_madansky_upper_bound
-- name    : StochasticProg.Bounds.thm2_edmundson_madansky_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:55:00.530487+00:00
-- url     : https://prove2.me/theorems/045e6e2b-803a-4245-8023-385c26cda59f
-- title:
--   Chapter 8, Theorem 2 — Edmundson-Madansky upper bound
-- statement:
--   **Chapter 8, Theorem 2** (Birge & Louveaux, pp. 347-348): the Edmundson-Madansky upper bound.
--
--   Fix a probability space $(\Omega,\mu)$, a complete normed real vector space $E$, a compact set
--   $\Xi\subseteq E$, and a random vector $\xi:\Omega\to E$ with $\xi(\omega)\in\Xi$ almost surely
--   and $\xi$ Bochner-integrable. Fix $\alpha$, $D\subseteq\alpha$, $x\in D$, and
--   $g:\alpha\to E\to\mathbb R$ with $g(x,\cdot)$ convex and continuous on $\Xi$ and
--   $\omega\mapsto g(x,\xi(\omega))$ integrable. Let `Ext` be a type standing for the extreme
--   points $\mathrm{ext}\,\Xi$ of $\mathrm{co}\,\Xi$, carrying the *discrete* measurable-space
--   structure (every subset measurable, matching the book's "Borel field ... the collection of
--   all subsets"), and `toE : Ext → E` an embedding whose range is exactly $\mathrm{ext}\,\Xi$
--   (formally `(convexHull ℝ Ξ).extremePoints ℝ`). Let `φ : E → Measure Ext` assign to every
--   $e\in\Xi$ a probability measure `φ e` on `Ext` with barycenter $e$,
--   $$
--   \int_{\mathrm{Ext}} \mathrm{toE}(y)\,\varphi(e)(dy) = e \qquad (e\in\Xi),
--   $$
--   such that $\omega\mapsto\varphi(\xi(\omega))(A)$ is measurable for every
--   $A\subseteq\mathrm{Ext}$ (the disintegration hypothesis). Let `μExt` be a probability measure
--   on `Ext` satisfying the book's defining equation (2.6),
--   $$
--   \mu\mathrm{Ext}(A) = \int_\Omega \varphi(\xi(\omega))(A)\,d\mu(\omega) \qquad
--   (A\subseteq\mathrm{Ext}),
--   $$
--   and suppose $y\mapsto g(x,\mathrm{toE}(y))$ is $\mu\mathrm{Ext}$-integrable. Then
--   $$
--   \int_\Omega g(x,\xi(\omega))\,d\mu(\omega) \;\le\;
--   \int_{\mathrm{Ext}} g(x,\mathrm{toE}(y))\,d\mu\mathrm{Ext}(y) ,
--   $$
--   i.e. $\mathbb E(g(x)) \le \int_{\mathrm{ext}\Xi} g(x,e)\,\lambda(de)$, the book's (2.5).
--
--   **Formalization Note** `μExt` (the book's $\lambda$, renamed since `λ` is a reserved Lean
--   keyword) is taken as a hypothesis satisfying its defining equation rather than constructed
--   from `φ`, since the book's own proof does not construct it either — constructing a measure
--   from a set function via eq. (2.6) is a separate, book-external piece of measure theory. The
--   barycenter condition on `φ` and the measurability of $\omega\mapsto\varphi(\xi(\omega))(A)$
--   are both load-bearing hypotheses the book's proof genuinely uses, not boilerplate.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 347-348, Chapter 8, Theorem 2 (eq. 2.4-2.6)

import Mathlib

open MeasureTheory

namespace StochasticProg.Bounds

variable {Ω E α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Chapter 8, Theorem 2 (Birge & Louveaux, pp. 347-348): the Edmundson-Madansky upper bound.
`Ext` stands for the extreme points `extΞ` of `co Ξ`, carrying the Borel field of *all* its
subsets (`hExtσ`) that the book specifies; `toE` embeds `Ext` into `E` with range exactly
`extΞ`. For every `e ∈ Ξ`, `φ e` is a probability measure on `Ext` with barycenter `e`
(eq. 2.4) and `ω ↦ φ (ξ ω) A` measurable for every `A` (the disintegration hypothesis); `μExt`
is the probability measure on `Ext` defined from `φ` and `ξ` by eq. (2.6). Then
`E(g(x)) ≤ ∫_{extΞ} g(x, e) μExt(de)` (eq. 2.5). -/
theorem thm2_edmundson_madansky_upper_bound
    {Ξ : Set E} (hΞcompact : IsCompact Ξ)
    {Ext : Type*} [MeasurableSpace Ext] (hExtσ : ∀ A : Set Ext, MeasurableSet A)
    (toE : Ext → E) (hExt : Set.range toE = (convexHull ℝ Ξ).extremePoints ℝ)
    {ξ : Ω → E} (hξrange : ∀ᵐ ω ∂μ, ξ ω ∈ Ξ) (hξint : Integrable ξ μ)
    {D : Set α} {x : α} (hx : x ∈ D) {g : α → E → ℝ}
    (hgconv : ConvexOn ℝ Ξ (g x)) (hgcont : ContinuousOn (g x) Ξ)
    (hgint : Integrable (fun ω => g x (ξ ω)) μ)
    (φ : E → Measure Ext) [∀ e, IsProbabilityMeasure (φ e)]
    (hbary : ∀ e ∈ Ξ, ∫ y : Ext, toE y ∂(φ e) = e)
    (hφmeas : ∀ A : Set Ext, Measurable fun ω => (φ (ξ ω)) A)
    (μExt : Measure Ext) [IsProbabilityMeasure μExt]
    (hμExtdef : ∀ A : Set Ext, μExt A = ∫⁻ ω, (φ (ξ ω)) A ∂μ)
    (hgeint : Integrable (fun y : Ext => g x (toE y)) μExt) :
    ∫ ω, g x (ξ ω) ∂μ ≤ ∫ y : Ext, g x (toE y) ∂μExt := by sorry

end StochasticProg.Bounds
