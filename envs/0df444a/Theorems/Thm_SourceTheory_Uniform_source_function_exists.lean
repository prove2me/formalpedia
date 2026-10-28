-- Prove2me | Theorems.Thm_SourceTheory_Uniform_source_function_exists
-- name    : SourceTheory.Uniform.source_function_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T09:14:37.84393+00:00
-- url     : https://prove2.me/theorems/5f7db941-6c26-461b-a185-8a1b724b7aeb
-- title:
--   Equation (5), p. 8771 — a uniform source has a continuous source function: W = w_S ∘ P_S
-- statement:
--   Let $\succcurlyeq$, $U$ and $W$ satisfy structural Assumption 1 on the events $\mathcal E$, and let $\mathcal S$ be a source (a subalgebra of $\mathcal E$ on which $W$ is convex ranged). Suppose $\mathcal S$ is **uniform** with a-neutral probability measure $P$: $P$ is a (finitely additive) probability measure on $\mathcal S$ and stochastic dominance (2) with respect to $P$ holds for all acts from $\mathcal S$,
--   $$\big[\forall \alpha:\ P(x \succcurlyeq \alpha) \ge P(y \succcurlyeq \alpha)\big] \Rightarrow x \succcurlyeq y .$$
--   Then $\mathcal S$ has a **source function**: there is a continuous probability weighting function $w_{\mathcal S}:[0,1]\to[0,1]$ (strictly increasing, $w_{\mathcal S}(0)=0$, $w_{\mathcal S}(1)=1$) such that
--   $$W(E) = w_{\mathcal S}\big(P(E)\big) \quad \text{for all } E \in \mathcal S. \qquad (5)$$
--
--   The paper states (5) for uniform sources and says its proof is identical to that of Observation 1 (for risk): define $w(p)=W(E)$ for $E$ with $P(E)=p$, well defined by stochastic dominance; convex rangedness gives that the domain of $w$ is all of $[0,1]$ and that $w$ is strictly increasing (Online Appendix A for finitely additive $P$); surjectivity then gives continuity. This is the step of the proof of Theorem 4 that turns uniformity of a source (from Theorem 1) into the existence of its source function $w_{\mathcal S}$.
-- source:
--   Baillon, Bleichrodt, Li, Wakker (2025), Source Theory: A Tractable and Positive Ambiguity Theory, Management Science 71(10), §4, Equation (5), p. 8771 (proof as for Observation 1, p. 8779 / App. B; Online Appendix A)

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.Uniform

/-- Equation (5) (Baillon et al. 2025, p. 8771): under structural Assumption 1, a uniform source `𝒮`
with a-neutral probability measure `P` has a source function: a continuous probability weighting
function `w` with `W = w ∘ P` on `𝒮`. ("The proof is identical to Observation 1 and is omitted.") -/
theorem source_function_exists {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮) (P : Set S → ℝ) (hP : IsUniformWith pref U 𝒮 P) :
    ∃ w : ℝ → ℝ, IsSourceFunction W 𝒮 P w := by sorry

end SourceTheory.Uniform
