-- Prove2me | Theorems.Thm_StochCompStatics_theorem_1
-- name    : StochCompStatics.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:48.589542+00:00
-- url     : https://prove2.me/theorems/c497c873-0709-4986-a2ee-56a5ceecb218
-- title:
--   Theorem 1 — $P_2$ $D$-preserving and $P_2(s,\cdot)\succeq_D P_1(s,\cdot)$ give $\mu_2^t\succeq_D\mu_1^t$ for all $t$
-- statement:
--   Let $S$ be a measurable space, $D$ a set of functions $S\to\mathbb R$, and $P_1,P_2$ transition probabilities on $S$. Let $\mu_i^t$ be the law in period $t$ of the chain with transition $P_i$ started at the same state $s(1)$. Assume that every measurable $f\in D$ is integrable against every $\mu_i^t$ and every $P_i(s,\cdot)$. If $P_2$ is $D$-preserving and $P_2(s,\cdot)\succeq_D P_1(s,\cdot)$ for all $s\in S$, then
--   $$
--   \mu_2^t\succeq_D\mu_1^t\qquad\text{for all }t\in\mathbb N.
--   $$
--
--   This is the paper's general comparison of Markov chains; with $D$ the increasing functions it turns a one-step comparison of transitions into a comparison of the state distributions in all future periods.
--
--   Differences from the source:
--   - generalization: Pᵢ(s, B) = pᵢ(s, g(s, eᵢ), B) for parameters e₁ ⪯ e₂ of a partially ordered set E → two arbitrary Markov kernels P₁, P₂ on S; no order on S or E; reason: E and eᵢ only name the two kernels, and the proof uses no order; the paper's transitions are instances
--   - reading: footnote 9: all functions are assumed to be integrable → hD: every measurable f ∈ D is integrable against every µᵗᵢ and every Pᵢ(s, ·); reason: the integrals in the definition of ⪰_D and of D-preserving are those the paper writes
--   - encoding: for all Borel measurable f ∈ D such that the integrals exist → for all measurable f ∈ D integrable against both measures; reason: existence of the integral read as integrability
--   - generalization: Pᵢ D-preserving: f ∈ D implies ∫ f(s′)Pᵢ(s, ds′) ∈ D → the implication only for measurable f ∈ D; reason: a weaker hypothesis; the paper's integrals are of Borel functions
--   - encoding: periods t ∈ ℕ = {1, 2, …}, µ¹ = δ_{s(1)} → t : ℕ starting at 0, stateLaw p g s₁ 0 = δ_{s₁}; reason: Lean index t is the paper's period t + 1; same statements
-- source:
--   Light, Stochastic Comparative Statics in Markov Decision Processes, arXiv:1904.05481v2, Theorem 1, p.9 (proof: Appendix §6.1, p.18)

import Mathlib
import Definitions.Def_StochCompStatics_ChainLaw

namespace StochCompStatics

open MeasureTheory ProbabilityTheory

/-- Theorem 1 (Light, Stochastic Comparative Statics in Markov Decision Processes,
arXiv:1904.05481v2, §3.1, p.9): let `D ⊆ ℝ^S`. If `P₂` is `D`-preserving and
`P₂(s, ·) ⪰_D P₁(s, ·)` for all `s ∈ S`, then `µ^t_2 ⪰_D µ^t_1` for all `t ∈ ℕ`, where `µ^t_i` is
the law of period `t` of the chain with transition `Pᵢ` started at `s(1)`.

**Formalization Note** The paper's transitions are `Pᵢ(s, B) = pᵢ(s, g(s, eᵢ), B)` for parameters
`e₁ ⪯ e₂` of a poset `E`; the statement is for two arbitrary Markov kernels `P₁, P₂` on `S`, which
covers them (`E` and `eᵢ` only name the kernels). The Lean index `t` is the paper's period `t + 1`.
Footnote 9 ("all functions are assumed to be integrable") is the hypothesis `hD`: every measurable
`f ∈ D` is integrable against every `µ^t_i` and every `Pᵢ(s, ·)`. -/
theorem theorem_1 {S : Type*} [MeasurableSpace S] (D : Set (S → ℝ)) (P₁ P₂ : Kernel S S)
    [IsMarkovKernel P₁] [IsMarkovKernel P₂] (s₁ : S)
    (hD : ∀ f ∈ D, Measurable f →
      (∀ t, Integrable f (chainLaw P₁ s₁ t) ∧ Integrable f (chainLaw P₂ s₁ t)) ∧
      ∀ s, Integrable f (P₁ s) ∧ Integrable f (P₂ s))
    (hpres : IsDPreserving D P₂) (hcomp : ∀ s, DDominates D (P₂ s) (P₁ s)) :
    ∀ t, DDominates D (chainLaw P₂ s₁ t) (chainLaw P₁ s₁ t) := by sorry

end StochCompStatics
