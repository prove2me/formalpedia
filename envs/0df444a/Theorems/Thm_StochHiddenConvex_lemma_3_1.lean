-- Prove2me | Theorems.Thm_StochHiddenConvex_lemma_3_1
-- name    : StochHiddenConvex.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:47.893295+00:00
-- url     : https://prove2.me/theorems/a9aa5034-83e1-40c9-bc21-0b86025c4e33
-- title:
--   Lemma 3.1: $g(\Pi_{\mathcal X}(x))=\Pi_{\mathcal U}(g(x))$ for every $x\in\mathbb R^d$
-- statement:
--   Let $\mathcal X=\prod_i[\underline X_i,\bar X_i]$ be a box and $\phi(x,\xi)=(\phi_i(x_i,\xi_i))_i$ separable, with each $\phi_i(\cdot,\xi_i)$ non-decreasing on $\mathbb R$ for almost every $\xi$ and $g(y)=\mathbb E\phi(y,\xi)$ finite at the corners of $\mathcal X$ and at the point $x$ below. Let $\mathcal U=\prod_i[g_i(\underline X_i),g_i(\bar X_i)]$. Then for **every** $x\in\mathbb R^d$,
--   $$g\big(\Pi_{\mathcal X}(x)\big)=\Pi_{\mathcal U}\big(g(x)\big).$$
--
--   Projection onto the box and the transformation $g$ commute. This is what lets the proof of Theorem 3.2 treat the projected update $x^{t+1}=\Pi_{\mathcal X}(x^t-\gamma v_F(x^t))$ as a projected step $u^{t+1}=\Pi_{\mathcal U}(g(x^t-\gamma v_F(x^t)))$ in the $u$-space.
--
--   Differences from the source:
--   - generalization: for any x ∈ 𝒳 → for every x ∈ ℝ^d; reason: for x ∈ 𝒳 the printed claim is Case I of the proof; the proof of Theorem 3.2 applies the lemma at x^t − γv_F(x^t) ∉ 𝒳 (p.38, step (b)); the statement specializes to the printed one
--   - generalization: Assumption 2.1(a)(b) → Assumption 2.1(a) (independence) dropped; reason: the proof does not use it; fewer hypotheses specialize to the printed ones
--   - reading: Assumption 2.1(b), stated without a domain for x → ϕᵢ(·, ξᵢ) non-decreasing on all of ℝ (MonotoneGlobal); reason: the proof applies Lemma 3.1 outside 𝒳 (Cases II–III, p.32, used at x^t − γv_F(x^t), p.38)
--   - reading: for any ξ ∈ Ξ (Assumptions 2.1(b), 2.2(c)) → for ℙ-almost every ξ; reason: Ξ ⊆ ℝ^d is the unspecified set of values of ξ, a set of probability one; the conditions enter only through expectations
--   - encoding: g(x) = 𝔼ϕ(x, ξ) at the point x and at the corners of 𝒳 → ϕᵢ(·, ξᵢ) integrable at X̲ᵢ, X̄ᵢ and at the given xᵢ; reason: the statement evaluates g there (for x ∈ 𝒳 this is the box integrability of g); excludes only data for which the statement is undefined
--   - encoding: Π_𝒳(x) := arg min_{y∈𝒳} ‖y − x‖² and Π_𝒰 → coordinatewise clamping to the box; reason: the Euclidean projection onto a box (X̲ᵢ ≤ X̄ᵢ)
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Lemma 3.1, p.15; proof Appendix A.3, pp.32–33

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_G
import Definitions.Def_StochHiddenConvex_Model_GlobalModel

open MeasureTheory

namespace StochHiddenConvex

/-- **Lemma 3.1 (projection and transformation commute).** Chen, He, Hu & Ye,
arXiv:2205.01774v3, Lemma 3.1, p.15 (proof Appendix A.3, pp.32–33): "Suppose that 𝒳 is a box
constraint and Assumption 2.1(a)(b) holds. For any x ∈ 𝒳, we have g(Π_𝒳(x)) = Π_𝒰(g(x))."

Stated for **every** `x ∈ ℝ^d`: for `x ∈ 𝒳` the printed claim is Case I of the proof, and the
proof of Theorem 3.2 (p.38, step (b)) applies the lemma at `x^t − γ v_F(x^t)`, outside `𝒳`.

**Formalization Note.** `ϕᵢ(·, ξᵢ)` is non-decreasing on all of `ℝ` for almost every `ξ`
(`MonotoneGlobal`, used in Cases II–III, p.32), and `gᵢ = 𝔼ϕᵢ(·, ξᵢ)` is defined at `X̲ᵢ`, `X̄ᵢ`
and at the point `xᵢ` where the lemma is applied (for `x ∈ 𝒳` this is the box integrability of
`g`). Independence (2.1(a)) is not needed and is dropped. `Π_𝒳` and `Π_𝒰` are
coordinatewise clamping. -/
theorem lemma_3_1 {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P]
    (hmono : M.MonotoneGlobal) (x : Vec d)
    (hint : ∀ i, Integrable (fun s => M.phi i (M.lo i) (s i)) M.P ∧
      Integrable (fun s => M.phi i (M.hi i) (s i)) M.P ∧
      Integrable (fun s => M.phi i (x i) (s i)) M.P) :
    M.g (M.projBox x) = M.projU (M.g x) := by sorry

end StochHiddenConvex
