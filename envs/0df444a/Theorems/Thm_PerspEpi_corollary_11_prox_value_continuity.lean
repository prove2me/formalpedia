-- Prove2me | Theorems.Thm_PerspEpi_corollary_11_prox_value_continuity
-- name    : PerspEpi.corollary_11_prox_value_continuity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:52.522326+00:00
-- url     : https://prove2.me/theorems/63d50810-b5ed-4678-a234-4178cb6b9090
-- title:
--   Corollary 11 (corrected: $\eta$ finite iff $P_{\operatorname{cl}(\operatorname{dom} f)}(\bar x)\in\operatorname{dom} f$): continuity properties of the proximal value
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space, $f\in\Gamma_0(E)$ and $\bar x\in E$, and let $\eta = \eta^f_{\bar x}$ be the proximal value function ($f(P_\lambda f(\bar x))$ for $\lambda>0$, $f(P_{\operatorname{cl}(\operatorname{dom} f)}(\bar x))$ for $\lambda\le0$). Then:
--
--   1. **(a)** $\eta$ is decreasing (nonincreasing) and continuous on $\mathbb R$ as an extended-real-valued function, and it is finite-valued if and only if $P_{\operatorname{cl}(\operatorname{dom} f)}(\bar x)\in\operatorname{dom} f$;
--   2. **(b)** $\eta$ is finite and locally Lipschitz on $\mathbb R_{++}$;
--   3. **(c)** if $\bar x\in\operatorname{dom}\partial f$, then $\eta$ is finite and locally Lipschitz on all of $\mathbb R$.
--
--   The function $\eta$ is (minus) the derivative of $\bar\varphi^f_{\bar x}$ (Corollary 12), and its regularity at $\lambda = 0$ governs the scalar root-finding problem of Corollary 14.
--
--   **Formalization Note** Continuity in (a) is in the order topology of `EReal`; (b) and (c) are stated for the real values of $\eta$ together with their finiteness.
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - correction: η finite-valued if (and only if) P_cl(dom f)(x̄) = x̄ ∈ dom f → η finite-valued iff P_cl(dom f)(x̄) ∈ dom f; reason: the printed 'only if' is false: for E = ℝ, f = δ_[0,1], x̄ = 2, η ≡ 0 is finite but P_cl(dom f)(2) = 1 ≠ 2; since η(λ) < +∞ for λ > 0, finiteness is exactly P_cl(dom f)(x̄) ∈ dom f, and the printed 'if' is its special case
--   - reading: decreasing → Antitone (non-strict); reason: η is constant on λ ≤ 0, so strict decrease is impossible
--   - encoding: η locally Lipschitz on ℝ++ (resp. ℝ) → finiteness of η there and LocallyLipschitzOn of λ ↦ (η λ).toReal; reason: Lipschitz continuity presupposes finite values; the finiteness clause is true and makes toReal faithful
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Corollary 11, p.19

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_projC
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_PerspEpi_eta

open Filter Topology

namespace PerspEpi

/-- **Corollary 11 (Continuity properties of the proximal value)**, with the finiteness criterion of
(a) corrected. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.19: "Let f ∈ Γ0(E) and fix x̄ ∈ E. Then the following hold:
(a) η^f_x̄ is decreasing, continuous (possibly in an extended real-valued sense), and finite-valued if
(and only if) P_cl(dom f)(x̄) = x̄ ∈ dom f. (b) η^f_x̄ is locally Lipschitz on ℝ₊₊.
(c) If x̄ ∈ dom ∂f, then the assertion in (b) holds on ℝ."

**Correction.** The printed "only if" is false: for `E = ℝ`, `f = δ_[0,1]`, `x̄ = 2`, `η ≡ 0` is
finite-valued but `P_cl(dom f)(2) = 1 ≠ 2`. Since `η(λ) = f(P_λ f(x̄)) < +∞` for every `λ > 0`, the
true criterion is `η` finite-valued **iff** `P_cl(dom f)(x̄) ∈ dom f`, stated here; the printed
"if" direction is its special case `P_cl(dom f)(x̄) = x̄`.

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`. `η^f_x̄` is `PerspEpi.eta f x̄ : ℝ → EReal`; "decreasing" is non-strict (`Antitone`);
continuity is in the topology of `EReal`. (b) and (c) are stated for the real values `η(λ).toReal`,
together with the finiteness of `η` on the set in question (which (b) and (c) presuppose). -/
theorem corollary_11_prox_value_continuity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) (xbar : E) :
    -- (a)
    (Antitone (eta f xbar) ∧ Continuous (eta f xbar) ∧
      ((∀ lam : ℝ, eta f xbar lam ≠ ⊤) ↔ projC (closure (AubinLipschitz.effDom f)) xbar ∈ AubinLipschitz.effDom f)) ∧
    -- (b)
    ((∀ lam : ℝ, 0 < lam → eta f xbar lam ≠ ⊤) ∧
      LocallyLipschitzOn (Set.Ioi 0) (fun lam : ℝ => (eta f xbar lam).toReal)) ∧
    -- (c)
    ((MoreauChance.Consistency.subdiff f xbar).Nonempty →
      (∀ lam : ℝ, eta f xbar lam ≠ ⊤) ∧
        LocallyLipschitz (fun lam : ℝ => (eta f xbar lam).toReal)) := by sorry

end PerspEpi
