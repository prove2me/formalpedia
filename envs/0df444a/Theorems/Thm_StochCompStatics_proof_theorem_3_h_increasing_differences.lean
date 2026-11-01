-- Prove2me | Theorems.Thm_StochCompStatics_proof_theorem_3_h_increasing_differences
-- name    : StochCompStatics.proof_theorem_3_h_increasing_differences
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:37.247031+00:00
-- url     : https://prove2.me/theorems/73afb353-71a6-4c02-93bb-7335f1491d16
-- title:
--   Proof of Theorem 3, p.21 — $h(s,a,\beta,f)$ has increasing differences in $(a,\beta)$ and in $(s,\beta)$
-- statement:
--   Let $E=(0,1)$ be the set of discount factors with its usual order, let $p$ be monotone, and let $f(s,\beta)$ be increasing in $s$ and have increasing differences in $(s,\beta)$ on $S\times(0,1)$, with each $f(\cdot,\beta)$ measurable and integrable against every $p(s,a,\cdot)$, $a\in A$. Then
--   $$
--   h(s,a,\beta,f)=r(s,a)+\beta\int_S f(s',\beta)\,p(s,a,ds')
--   $$
--   has increasing differences in $(a,\beta)$ on $A\times(0,1)$ for every $s$, and in $(s,\beta)$ on $S\times(0,1)$ for every $a\in A$: for $a_1\le a_2$ and $\beta_1\le\beta_2$,
--   $$
--   h(s,a_2,\beta_2,f)-h(s,a_1,\beta_2,f)\ge h(s,a_2,\beta_1,f)-h(s,a_1,\beta_1,f),
--   $$
--   and likewise in $s$.
--
--   Together with Propositions 5 and 6 this shows that every value iterate has increasing differences in $(s,\beta)$.
--
--   Differences from the source:
--   - generalization: under Assumption 1 (the standing hypothesis of the proof of Theorem 3) → only p monotone; no hypothesis on r; reason: r(s, a) does not depend on β and cancels from both differences; the paper's setting is an instance
--   - generalization: state space S ⊆ ℝⁿ a Borel set with the componentwise order → any measurable space S with a partial order; reason: the paper's S with the Borel σ-algebra and the componentwise order is an instance
--   - encoding: action space A ⊆ ℝ, p and r defined on S × A → A : Set ℝ, p a Markov kernel on S × ℝ, r : S → ℝ → ℝ, every hypothesis on p and r imposed for a ∈ A only; reason: values of p and r at actions outside A are never used; same instances
--   - reading: p monotone: for every increasing f, ∫ f(s′)p(s, a, ds′) is increasing in (s, a) → for every increasing measurable f integrable against every p(s, a), a ∈ A, the integral is monotone on S × A; reason: footnote 9: the integral of f exists only for such f
--   - reading: f ∈ B(S × E), all functions integrable (footnote 9) → each f(·, β), β ∈ (0, 1), measurable and integrable against every p(s, a), a ∈ A; reason: the integrals in h are those the paper writes
-- source:
--   Light, Stochastic Comparative Statics in Markov Decision Processes, arXiv:1904.05481v2, Proof of Theorem 3, display, p.21 (Appendix §6.2)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn
import Definitions.Def_StochCompStatics_Model

namespace StochCompStatics

open MeasureTheory ProbabilityTheory Supermodularity.Monotonicity

/-- Proof of Theorem 3(i), display (Light, Stochastic Comparative Statics in Markov Decision
Processes, arXiv:1904.05481v2, Appendix §6.2, p.21): let `E = (0, 1)` be the set of discount
factors and `f ∈ B(S × E)` have increasing differences in `(s, β)` and be increasing in `s`. If `p`
is monotone, then `h(s, a, β, f) = r(s, a) + β ∫ f(s', β) p(s, a, ds')` has increasing differences
in `(a, β)` and in `(s, β)`.

**Formalization Note** `f β` is the function `s ↦ f(s, β)`. For each `β ∈ (0, 1)` it is measurable
and integrable against every `p(s, a)`, `a ∈ A` (footnote 9). Increasing differences in `(a, β)`
are on `A × (0, 1)` for each `s`, and in `(s, β)` on `S × (0, 1)` for each `a ∈ A`. -/
theorem proof_theorem_3_h_increasing_differences {S : Type*} [MeasurableSpace S] [PartialOrder S]
    (A : Set ℝ) (p : Kernel (S × ℝ) S) [IsMarkovKernel p] (r : S → ℝ → ℝ) (f : ℝ → S → ℝ)
    (hp : IsMonotoneKernel A p)
    (hf : ∀ β ∈ Set.Ioo (0 : ℝ) 1, Monotone (f β) ∧ Measurable (f β) ∧
      ∀ s, ∀ a ∈ A, Integrable (f β) (p (s, a)))
    (hID : IncreasingDifferencesOn (fun s β => f β s) (Set.univ ×ˢ Set.Ioo 0 1)) :
    (∀ s, IncreasingDifferencesOn (fun a β => h p r β (f β) s a) (A ×ˢ Set.Ioo 0 1)) ∧
    (∀ a ∈ A, IncreasingDifferencesOn (fun s β => h p r β (f β) s a)
      (Set.univ ×ˢ Set.Ioo 0 1)) := by sorry

end StochCompStatics
