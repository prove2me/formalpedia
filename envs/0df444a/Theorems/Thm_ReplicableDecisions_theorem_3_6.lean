-- Prove2me | Theorems.Thm_ReplicableDecisions_theorem_3_6
-- name    : ReplicableDecisions.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:22.481204+00:00
-- url     : https://prove2.me/theorems/ad741ac3-11ea-41a3-8ef4-716f5cd1b1a7
-- title:
--   Theorem 3.6 — selection to samples: $A(S;R)=f_R(\widehat P(S))$
-- statement:
--   Let $\mathcal Y$ be finite, $r>0$, $0<\delta<1$, and let $G$ contain $G_{<r}$. Draw a selector $f_R$ independently of the data, and let $n\ge r^{-2}\log(M/\delta)$. Then $A(S;R)=f_R(\widehat P(S))$ has the following guarantees at each $P\in\mathcal P$.
--
--   1. If $\Pr_R[P\in B_G(f_R)]\le\eta$, then $\mathrm{err}_P(A)\le\eta+\delta$ and $\mathrm{rep}_P(A)\le\eta+2\delta$.
--   2. If every $f_R$ is neighborhood correct and $\Pr_R[P\in\partial_Gf_R]\le\eta$, then $\mathrm{err}_P(A)\le\delta$ and $\mathrm{rep}_P(A)\le\eta+2\delta$.
--
--   The second part is what separates accuracy from replication in the goal: the accuracy error no longer depends on $\eta$.
--
--   Differences from the source:
--   - encoding: a known family P = {P1, …, PM} of distinct distributions on a finite set Z → an `Experiment ι Z`: an injective table of probability vectors over a finite index type, with Z in `Type` and M = `Fintype.card ι`; reason: models are named by index; the reused Bhattacharyya coefficient takes a type in `Type`, which loses no finite Z
--   - encoding: probabilities over S, S′ ∼ Pⁿ and the seed R → finite sums over samples `Fin n → Z` of products of table entries times seed-measure terms `μ.real`; reason: the data side is finite; the same numbers
--   - generalization: a maximum-likelihood model with fixed tie-breaking → any function `mle` of the sample selecting a likelihood maximizer; reason: the proof bounds the event pointwise in the sample and never uses how ties are broken; every fixed tie-breaking is such a function
--   - encoding: a selector f_R drawn independently of the data → `f : Ω → ι → Y` on a probability space, with `{ω | f ω i = y}` measurable; reason: independence is the product form of err and rep
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Theorem 3.6, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_IsMaxLikelihood
import Definitions.Def_ReplicableDecisions_weakGraph
import Definitions.Def_ReplicableDecisions_boundary

open MeasureTheory

namespace ReplicableDecisions

/-- **Theorem 3.6 (Selection-to-samples conversion).** Chen, *Replicable Decisions in Finite
Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 3.6, p.13 (PDF p.15). Let `Y` be finite,
`r > 0`, `0 < δ < 1`, `G` contain `G_{<r}`, `f_R` a selector drawn independently of the data, and
`n ≥ r⁻² log(M/δ)`. Then `A(S; R) = f_R(P̂(S))` has, at each `P`: (1) if `Pr_R[P ∈ B_G(f_R)] ≤ η`, then
`err_P(A) ≤ η + δ` and `rep_P(A) ≤ η + 2δ`; (2) if every `f_R` is neighborhood correct and
`Pr_R[P ∈ ∂_G f_R] ≤ η`, then `err_P(A) ≤ δ` and `rep_P(A) ≤ η + 2δ`.

**Formalization Note.** `f : Ω → ι → Y` is a random selector on an arbitrary probability space, and the
independence from the data is the product form of `err` and `rep`. -/
theorem theorem_3_6 {ι : Type*} {Z : Type} {Y : Type*} [Fintype ι] [Fintype Z]
    [Fintype Y] (E : Experiment ι Z) (Γ : ι → Set Y) (hΓ : ∀ i, (Γ i).Nonempty)
    (G : SimpleGraph ι) {r δ : ℝ} (hr : 0 < r) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hG : strictGraph E r ≤ G) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ι → Y) (hf : ∀ i y, MeasurableSet {ω | f ω i = y}) {n : ℕ}
    (hn : Real.log ((Fintype.card ι : ℝ) / δ) / r ^ 2 ≤ n) (mle : (Fin n → Z) → ι)
    (hmle : IsMaxLikelihood E mle) (i : ι) (η : ℝ) :
    (μ.real {ω | i ∈ badSet G Γ (f ω)} ≤ η →
        err E Γ μ (fun x ω => f ω (mle x)) i ≤ η + δ ∧
          rep E μ (fun x ω => f ω (mle x)) i ≤ η + 2 * δ) ∧
      ((∀ ω, NeighborhoodCorrect G Γ (f ω)) → μ.real {ω | i ∈ boundary G (f ω)} ≤ η →
        err E Γ μ (fun x ω => f ω (mle x)) i ≤ δ ∧
          rep E μ (fun x ω => f ω (mle x)) i ≤ η + 2 * δ) := by sorry

end ReplicableDecisions
