-- Prove2me | Theorems.Thm_PerspEpi_proposition_8_post_composition
-- name    : PerspEpi.proposition_8_post_composition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:36.79378+00:00
-- url     : https://prove2.me/theorems/c58dd121-2310-4750-be64-11efa470e0bf
-- title:
--   Proposition 8 (corrected: (c) needs $g$ nonconstant): Moreau envelope and proximal map of a post-composition $g\circ\psi$
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space, $g\in\Gamma_0(\mathbb R)$ increasing (nondecreasing), and $\psi\in\Gamma_0(E)$ with
--
--   $$
--   (\operatorname{ri}\operatorname{dom} g)\cap\psi(\operatorname{ri}\operatorname{dom}\psi)\ne\emptyset. \tag{29}
--   $$
--
--   Let $\bar x\in E$, $C = \operatorname{cl}(\operatorname{dom}\psi)$, $\bar\varphi^\psi_{\bar x}$ as in (27), and $g^*$ the conjugate of $g$. Then:
--
--   1. **(a)** The minimum below is attained and
--   $$
--   e_1(g\circ\psi)(\bar x) = -\min_{\lambda\ge0}\{g^*(\lambda)+\bar\varphi^\psi_{\bar x}(\lambda)\}.
--   $$
--   2. **(b)** $\operatorname{argmin}_{\lambda\ge0}\{g^*(\lambda)+\bar\varphi^\psi_{\bar x}(\lambda)\}\ne\emptyset$, and for every $\bar\lambda$ in it, $P_1(g\circ\psi)(\bar x) = P_1(\bar\lambda\cdot\psi)(\bar x)$.
--   3. **(c)** Suppose $g$ is not constant. If $\psi(P_C(\bar x))\notin\partial g^*(0)$, then every such minimizer is positive: $\operatorname{argmin}_{\lambda\ge0}\{g^*(\lambda)+\bar\varphi^\psi_{\bar x}(\lambda)\}\subset\mathbb R_{++}$. This is in particular the case if $P_C(\bar x)\notin\operatorname{dom}\psi$.
--
--   Applied to $g = \delta_{\mathbb R_-}$ and $\psi(x,\alpha) = f(x)-\alpha$ (so that $g\circ\psi = \delta_{\operatorname{epi} f}$), it yields the epigraphical projection formula of Corollary 14; with $\psi = f-\bar\alpha$ it yields the level-set projection of Corollary 13.
--
--   **Formalization Note** $e_1$ and $P_1$ are the envelope and the proximal map with parameter $1$, i.e. with the term $\frac12\|x-u\|^2$; (b) is stated as equality of the two argmin sets. $\operatorname{ri}$ is the relative (intrinsic) interior.
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - reading: g increasing → Monotone g (non-strict); reason: §7 applies the proposition to g = δ_{ℝ−}, which is nondecreasing but not strictly increasing
--   - reading: λ̄ · ψ for λ̄ = 0 (undefined on the page) → 0 · ψ := δ_dom ψ (scaleFn); reason: the convention of the paper's reference [10]; when 0 is a minimizer, P_C(x̄) ∈ dom ψ and both δ_dom ψ and δ_C give the proximal point P_C(x̄), so no instance changes
--   - encoding: P_1(g∘ψ)(x̄) = P_1(λ̄·ψ)(x̄) → GenNewtonSubgrad.ProxReg.prox (g∘ψ) 1 x̄ = GenNewtonSubgrad.ProxReg.prox (λ̄·ψ) 1 x̄ (equal argmin sets); reason: for nonconstant g, g∘ψ ∈ Γ0(E) and the left set is the singleton {P_1(g∘ψ)(x̄)}, so equality of sets is the page's equality with no choice of minimizer; for constant g both sides are the argmin of ½‖· − x̄‖² over dom ψ
--   - encoding: ψ(P_cl(dom ψ)(x̄)) ∉ ∂g*(0) → no real s with ψ(P_C x̄) = s lies in ∂g*(0) ⊆ ℝ; reason: ∂g*(0) is a set of reals; the condition is automatic when the value is +∞
--   - encoding: ri; (ri dom g) ∩ ψ(ri dom ψ) ≠ ∅ → intrinsicInterior ℝ; ∃ x ∈ ri dom ψ, ∃ r ∈ ri dom g, ψ x = r; reason: Mathlib's intrinsic interior is the relative interior
--   - encoding: e_1(g∘ψ) defined as a min → the infimum ⨅ in EReal (MoreauChance.Consistency.moreauEnv); reason: for g∘ψ ∈ Γ0(E) the minimum is attained, so the value is the same; for constant g the page's min need not exist and the infimum still satisfies (a)
--   - correction: (c) for every increasing g ∈ Γ0(ℝ) → (c) for g not constant (∃ s t, g s ≠ g t); reason: the printed (c) is false for constant g: for E = ℝ, g ≡ 0, ψ = −log on (0,∞) (+∞ elsewhere), x̄ = 0, (29) holds (ψ(1) = 0 with 1 ∈ ri dom ψ), P_cl(dom ψ)(0) = 0 ∉ dom ψ, and g* = δ_{0} makes argmin_{λ≥0}{g*(λ) + φ̄(λ)} = {0}, not inside ℝ₊₊; here g∘ψ = δ_(0,∞) is not closed; for constant g the hypothesis of (c) can only hold off dom ψ, so nothing else is lost, and §7 uses the nonconstant g = δ_{ℝ−}
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Proposition 8, p.22

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_ind
import Definitions.Def_PerspEpi_projC
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_PerspEpi_phiBar
import Definitions.Def_PerspEpi_postComp
import Definitions.Def_PerspEpi_scaleFn

open Filter Topology

namespace PerspEpi

/-- **Proposition 8 (Post-composition, Moreau envelopes, and proximal maps)**, with (c) corrected
to nonconstant `g`. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.22: "Let
g ∈ Γ0(ℝ) be increasing and let ψ ∈ Γ0(E) such that (ri dom g) ∩ ψ(ri dom ψ) ≠ ∅. (29)
Then the following properties hold.
(a) e_1(g ∘ ψ)(x̄) = −min_{λ≥0} {g*(λ) + φ̄^ψ_x̄(λ)}, where φ̄^ψ_x̄ is given by (27).
(b) P_1(g ∘ ψ)(x̄) = P_1(λ̄ · ψ)(x̄) for every λ̄ ∈ argmin_{λ≥0} {g*(λ) + φ̄^ψ_x̄(λ)} ≠ ∅.
(c) If ψ(P_cl(dom ψ)(x̄)) ∉ ∂g*(0), then argmin_{λ≥0} {g*(λ) + φ̄^ψ_x̄(λ)} ⊂ ℝ₊₊. This is, in
particular, the case if P_cl(dom ψ)(x̄) ∉ dom ψ."

**Correction of (c).** Both claims of (c) are false for constant `g`: for `E = ℝ`, `g ≡ 0`,
`ψ = −log` on `(0, ∞)` (`+∞` elsewhere) and `x̄ = 0`, (29) holds, `P_cl(dom ψ)(0) = 0 ∉ dom ψ`, and
`g* = δ_{0}` gives `argmin_{λ≥0}{g*(λ) + φ̄(λ)} = {0} ⊄ ℝ₊₊`. There `g ∘ ψ = δ_(0,∞)` is not closed,
against the paper's p.22 remark, and `int(dom g*) = ∅`, so the sum rule in step (i) of the proof of
(b) is unavailable. So (c) is stated for nonconstant `g`. Nothing else is lost: for constant `g`, `∂g*(0) = ℝ`, so the
hypothesis of (c) can only hold off `dom ψ`. §7's `g = δ_{ℝ₋}` is nonconstant. (a) and (b) hold for
constant `g` too and keep the printed hypotheses.

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`. `g ∘ ψ` is `PerspEpi.postComp` (`+∞` off `dom ψ`); "increasing" is non-strict
(`Monotone g`; §7 applies the result to `g = δ_{ℝ₋}`); `ri` is `intrinsicInterior ℝ`; `g*` is the
conjugate on `ℝ`. (a) asserts that the minimum over `λ ≥ 0` is attained. (b) is stated for the
argmin sets of `u ↦ ½‖x̄ − u‖² + h(u)` (the published argmin set `GenNewtonSubgrad.ProxReg.prox h 1 x̄`), so that `P_1(g ∘ ψ)(x̄)` and
`P_1(λ̄ · ψ)(x̄)` are the same singleton for nonconstant `g` (then `g ∘ ψ ∈ Γ0(E)`); `λ̄ · ψ` is `PerspEpi.scaleFn`, with `0 · ψ := δ_dom ψ`.
(c) "ψ(P_cl(dom ψ)(x̄)) ∉ ∂g*(0)" is read in `ℝ`: no real value of `ψ` at that point lies in
`∂g*(0)` (automatic if the value is `+∞`). -/
theorem proposition_8_post_composition {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (g : ℝ → EReal) (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g) (hg_mono : Monotone g)
    (ψ : E → EReal) (hψ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex ψ)
    (h29 : ∃ x ∈ intrinsicInterior ℝ (AubinLipschitz.effDom ψ), ∃ r ∈ intrinsicInterior ℝ (AubinLipschitz.effDom g),
      ψ x = (r : EReal))
    (xbar : E) :
    let A : Set ℝ := {l | 0 ≤ l ∧ ∀ m : ℝ, 0 ≤ m →
      MoreauChance.Consistency.conj g l + phiBar ψ xbar l ≤ MoreauChance.Consistency.conj g m + phiBar ψ xbar m}
    -- (a)
    (∃ l₀ ∈ A, MoreauChance.Consistency.moreauEnv (postComp g ψ) 1 xbar = -(MoreauChance.Consistency.conj g l₀ + phiBar ψ xbar l₀)) ∧
    -- (b)
    A.Nonempty ∧
    (∀ lbar ∈ A, GenNewtonSubgrad.ProxReg.prox (postComp g ψ) 1 xbar = GenNewtonSubgrad.ProxReg.prox (scaleFn lbar ψ) 1 xbar) ∧
    -- (c)
    ((∃ s t : ℝ, g s ≠ g t) →
      ((∀ s : ℝ, ψ (projC (closure (AubinLipschitz.effDom ψ)) xbar) = (s : EReal) → s ∉ MoreauChance.Consistency.subdiff (MoreauChance.Consistency.conj g) 0) →
        A ⊆ Set.Ioi 0) ∧
      (projC (closure (AubinLipschitz.effDom ψ)) xbar ∉ AubinLipschitz.effDom ψ → A ⊆ Set.Ioi 0)) := by sorry

end PerspEpi
