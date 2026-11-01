-- Prove2me | Theorems.Thm_StochCompStatics_corollary_1
-- name    : StochCompStatics.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:27.673009+00:00
-- url     : https://prove2.me/theorems/6b72ac77-212e-4869-98cd-9d6dbf59e2b5
-- title:
--   Corollary 1 — a higher, increasing policy under a monotone $p$ gives higher expected decisions $E^t$
-- statement:
--   Let $p$ be a monotone transition probability on $S\times A$, and let $g_1,g_2:S\to A$ be measurable policies with $g_1(s)\le g_2(s)$ for all $s$ and $g_2$ increasing in $s$. Let $\mu_i^t$ be the state law in period $t$ when the decision maker follows $g_i$ from the initial state $s(1)$, and assume $g_i$ is integrable against $\mu_i^t$. Then
--   $$
--   \mathbb E_2^t(g_2)=\int_S g_2\,d\mu_2^t\;\ge\;\int_S g_1\,d\mu_1^t=\mathbb E_1^t(g_1)\qquad\text{for all }t\in\mathbb N\text{ and every initial state }s(1)\in S.
--   $$
--
--   In the paper, $g_i=g(\cdot,e_i)$ for parameters $e_2\succeq e_1$ with $g(s,e)$ increasing in $e$; Corollary 1 is the step from comparative statics of the policy to comparative statics of the expected decisions in all future periods.
--
--   Differences from the source:
--   - generalization: g(s, e) increasing in e for all s, e₂ ⪰ e₁, g(s, e₂) increasing in s → two measurable policies g₁ ≤ g₂ pointwise, g₂ monotone; reason: the parameter only enters through g(s, e₁) ≤ g(s, e₂); the paper's policies are an instance
--   - encoding: policies with values in Γ(s) ⊆ A → hA₁, hA₂: gᵢ(s) ∈ A for every s; reason: a policy takes feasible actions, so its values lie in A
--   - generalization: state space S ⊆ ℝⁿ a Borel set with the componentwise order → any measurable space S with a partial order; reason: the paper's S with the Borel σ-algebra and the componentwise order is an instance
--   - encoding: action space A ⊆ ℝ, p and r defined on S × A → A : Set ℝ, p a Markov kernel on S × ℝ, r : S → ℝ → ℝ, every hypothesis on p and r imposed for a ∈ A only; reason: values of p and r at actions outside A are never used; same instances
--   - reading: p monotone: for every increasing f, ∫ f(s′)p(s, a, ds′) is increasing in (s, a) → for every increasing measurable f integrable against every p(s, a), a ∈ A, the integral is monotone on S × A; reason: footnote 9: the integral of f exists only for such f
--   - reading: footnote 9: all functions are assumed to be integrable → each gᵢ integrable against its own state laws µᵗᵢ; gᵢ measurable; reason: Eᵗᵢ is a Bochner integral, 0 for a non-integrable function; measurability makes µᵗᵢ the chain's law
--   - encoding: periods t ∈ ℕ = {1, 2, …}, µ¹ = δ_{s(1)} → t : ℕ starting at 0, stateLaw p g s₁ 0 = δ_{s₁}; reason: Lean index t is the paper's period t + 1; same statements
-- source:
--   Light, Stochastic Comparative Statics in Markov Decision Processes, arXiv:1904.05481v2, Corollary 1, p.9 (proof: Appendix §6.1, pp.18–19)

import Mathlib
import Definitions.Def_StochCompStatics_ChainLaw
import Definitions.Def_StochCompStatics_Model

namespace StochCompStatics

open MeasureTheory ProbabilityTheory

/-- Corollary 1 (Light, Stochastic Comparative Statics in Markov Decision Processes,
arXiv:1904.05481v2, §3.1, p.9): let `e₂ ⪰ e₁`, assume `g(s, e)` is increasing in `e` for all `s`,
`g(s, e₂)` is increasing in `s`, `p₁ = p₂ = p` and `p` is monotone. Then
`E^t_2(g(e₂)) ≥ E^t_1(g(e₁))` for all `t ∈ ℕ` and every initial state `s(1)`.

**Formalization Note** The two policies `g(·, e₁), g(·, e₂)` are two measurable functions
`g₁ ≤ g₂` with values in the action space `A` (`E` only enters through `g(s, e₁) ≤ g(s, e₂)`).
`E^t_i` is `expectedDecision p gᵢ s₁ t`, with Lean index `t` = period `t + 1`. Footnote 9 is the
integrability of each `gᵢ` against its own state laws. -/
theorem corollary_1 {S : Type*} [MeasurableSpace S] [PartialOrder S] (A : Set ℝ)
    (p : Kernel (S × ℝ) S) [IsMarkovKernel p] (g₁ g₂ : S → ℝ)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (hA₁ : ∀ s, g₁ s ∈ A) (hA₂ : ∀ s, g₂ s ∈ A)
    (hle : ∀ s, g₁ s ≤ g₂ s) (hmono : Monotone g₂) (hp : IsMonotoneKernel A p)
    (hint₁ : ∀ s₁ t, Integrable g₁ (stateLaw p g₁ s₁ t))
    (hint₂ : ∀ s₁ t, Integrable g₂ (stateLaw p g₂ s₁ t)) :
    ∀ s₁ t, expectedDecision p g₁ s₁ t ≤ expectedDecision p g₂ s₁ t := by sorry

end StochCompStatics
