-- Prove2me | Theorems.Thm_SuperPareto_step_d_decomposition
-- name    : SuperPareto.step_d_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:43.699289+00:00
-- url     : https://prove2.me/theorems/839c23d9-b974-4fe5-be55-dbf2d2fa4175
-- title:
--   Step (d), p.9 — $\sum\theta_iX_i\mathbb 1_{A_i}=\sum_S\mathbb 1_{B_S}\sum_{i\in S}\theta_iX_i$
-- statement:
--   Let $X_1,\dots,X_n$ be real functions on $\Omega$, $A_1,\dots,A_n\subseteq\Omega$ and $\theta_1,\dots,\theta_n\in\mathbb R$. For $S\subseteq[n]$ let
--
--   $$
--   B_S=\Big(\bigcap_{i\in S}A_i\Big)\cap\Big(\bigcap_{i\notin S}A_i^c\Big).
--   $$
--
--   Then pointwise on $\Omega$,
--
--   $$
--   \sum_{i=1}^n\theta_iX_i\mathbb 1_{A_i}=\sum_{S\subseteq[n]}\mathbb 1_{B_S}\sum_{i\in S}\theta_iX_i .
--   $$
--
--   The sets $B_S$ record which of the events occur; the identity splits the triggered portfolio of Theorem 1(ii) into the sub-portfolios $\sum_{i\in S}\theta_iX_i$ active on each $B_S$.
--
--   **Formalization Note** The subsets of $[n]$ are the `Finset`s of a finite index type.
--
--   Differences from the source:
--   - generalization: n ≥ 2 (standing assumption, p.4), (θ₁, …, θₙ) ∈ Δₙ, events A₁, …, Aₙ and random variables X₁, …, Xₙ → a finite index type of any size, arbitrary real θᵢ, arbitrary sets Aᵢ and arbitrary functions Xᵢ; reason: the identity is algebraic; the paper's case is a special case
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.3, step (d), p.9, "For S ⊆ [n], let BS = …. For (θ1, . . . , θn) ∈ ∆n, we write …"

import Mathlib

open MeasureTheory

namespace SuperPareto

/-- **Step (d): decomposition over the events `B_S`.** Chen, Embrechts, Wang, *An unexpected
stochastic dominance*, arXiv:2208.08471v4, §2.3, step (d), p.9: for `S ⊆ [n]` let
`B_S = (⋂_{i∈S} Aᵢ) ∩ (⋂_{i∈Sᶜ} Aᵢᶜ)`. For `(θ₁, …, θₙ) ∈ Δₙ`,
`∑ᵢ θᵢ Xᵢ 𝟙_{Aᵢ} = ∑_{S⊆[n]} 𝟙_{B_S} ∑_{i∈S} θᵢ Xᵢ`
pointwise on `Ω`.

**Formalization Note.** The identity holds for arbitrary real weights, arbitrary sets `Aᵢ` and
arbitrary functions `Xᵢ`; the subsets `S ⊆ [n]` are the `Finset`s of the `Fintype` `ι`. -/
theorem step_d_decomposition {Ω ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (A : ι → Set Ω)
    (θ : ι → ℝ) (ω : Ω) :
    ∑ i, θ i * (A i).indicator (X i) ω =
      ∑ S : Finset ι, ((⋂ i ∈ S, A i) ∩ (⋂ (i) (_ : i ∉ S), (A i)ᶜ)).indicator
        (fun ω' => ∑ i ∈ S, θ i * X i ω') ω := by sorry

end SuperPareto
