-- Prove2me | Theorems.Thm_SuperPareto_step_d_sum_identity
-- name    : SuperPareto.step_d_sum_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:47.246899+00:00
-- url     : https://prove2.me/theorems/25225415-2879-4055-95ba-7e82d686775a
-- title:
--   Step (d), p.10 — $\sum_SP(B_S)\sum_{i\in S}\theta_i=\sum_j\theta_jP(A_j)=P(A)$
-- statement:
--   Let $(\theta_1,\dots,\theta_n)\in\Delta_n$, let $A_1,\dots,A_n$ be events, $B_S=(\bigcap_{i\in S}A_i)\cap(\bigcap_{i\notin S}A_i^c)$ for $S\subseteq[n]$, and let $A$ be an event with $P(A)=\sum_i\theta_iP(A_i)$. Then $\sum_{i\in S}\theta_i\in[0,1]$ for every $S\subseteq[n]$, and
--
--   $$
--   \sum_{S\subseteq[n]}P(B_S)\sum_{i\in S}\theta_i=\sum_{j=1}^n\theta_j\sum_{S\subseteq[n],\,j\in S}P(B_S)=\sum_{j=1}^n\theta_jP(A_j)=P(A).
--   $$
--
--   Together with display (11) applied to the events $B_S$ and weights $c_S=\sum_{i\in S}\theta_i$, this gives $\sum_Sc_SX\mathbb 1_{B_S}\ge_{\mathrm{st}}X\mathbb 1_A$, the last step of the proof of Theorem 1(ii).
--
--   **Formalization Note** Probabilities are real (`P.real`); the subsets of $[n]$ are the `Finset`s of a finite index type.
--
--   Differences from the source:
--   - reading: the middle sum is printed ∑ⱼ θᵢ P(Aⱼ) → ∑ⱼ θⱼ P(Aⱼ); reason: the index of θ does not match the summation index; the preceding sum ∑ⱼ θⱼ ∑_{S∋j} P(B_S) fixes the meaning
--   - generalization: events A₁, …, Aₙ independent of (X₁, …, Xₙ) and an event A independent of X with P(A) = ∑θᵢP(Aᵢ) → any measurable sets Aᵢ and any set A₀ with P(A₀) = ∑θᵢP(Aᵢ), no random variable present; reason: the identity involves only the probabilities of the events; the paper's case is a special case
--   - generalization: n ≥ 2 random variables on an atomless probability space (standing assumptions, p.4) → a finite index type ι of any size (n = 1 allowed) on any probability space; reason: the paper's case n ≥ 2 on an atomless space is a special case; for n = 1 the statement holds trivially
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.3, step (d), p.10, "As ∑i∈S θi ∈ [0, 1] for any S ⊆ [n], and ∑S⊆[n] P(BS) ∑i∈S θi = …"

import Mathlib

open MeasureTheory

namespace SuperPareto

/-- **Step (d): the weights of the events `B_S` sum to `P(A)`.** Chen, Embrechts, Wang, *An
unexpected stochastic dominance*, arXiv:2208.08471v4, §2.3, step (d), p.10: `∑_{i∈S} θᵢ ∈ [0, 1]`
for every `S ⊆ [n]`, and
`∑_{S⊆[n]} P(B_S) ∑_{i∈S} θᵢ = ∑_j θⱼ ∑_{S∋j} P(B_S) = ∑_j θⱼ P(Aⱼ) = P(A)`,
where `B_S = (⋂_{i∈S} Aᵢ) ∩ (⋂_{i∈Sᶜ} Aᵢᶜ)` and `P(A) = ∑ θᵢ P(Aᵢ)`.

**Formalization Note.** The page prints the third sum as `∑_j θᵢ P(Aⱼ)`, with mismatched indices;
`∑_j θⱼ P(Aⱼ)` is meant. The index set is a `Fintype` `ι`; `Δₙ` is `stdSimplex ℝ ι`; `S ∋ j` is
`Finset.univ.filter (fun S => j ∈ S)`; events are measurable; probabilities are real (`P.real`).
`A₀` is the paper's `A`; only the value of `P(A)` is used. -/
theorem step_d_sum_identity {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) (hθ : θ ∈ stdSimplex ℝ ι)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (A₀ : Set Ω)
    (hA₀ : P.real A₀ = ∑ i, θ i * P.real (A i)) :
    (∀ S : Finset ι, 0 ≤ ∑ i ∈ S, θ i ∧ ∑ i ∈ S, θ i ≤ 1) ∧
      ∑ S : Finset ι, P.real ((⋂ i ∈ S, A i) ∩ (⋂ (i) (_ : i ∉ S), (A i)ᶜ)) * (∑ i ∈ S, θ i) =
        ∑ j, θ j * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => j ∈ S),
          P.real ((⋂ i ∈ S, A i) ∩ (⋂ (i) (_ : i ∉ S), (A i)ᶜ)) ∧
      ∑ j, θ j * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => j ∈ S),
          P.real ((⋂ i ∈ S, A i) ∩ (⋂ (i) (_ : i ∉ S), (A i)ᶜ)) =
        ∑ j, θ j * P.real (A j) ∧
      ∑ j, θ j * P.real (A j) = P.real A₀ := by sorry

end SuperPareto
