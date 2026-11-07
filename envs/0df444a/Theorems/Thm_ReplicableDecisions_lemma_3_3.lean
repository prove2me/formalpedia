-- Prove2me | Theorems.Thm_ReplicableDecisions_lemma_3_3
-- name    : ReplicableDecisions.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:07:20.33831+00:00
-- url     : https://prove2.me/theorems/e3132cef-0447-4571-8c61-701121bc458e
-- title:
--   Lemma 3.3 — canonical output: a valid rule gives $\Phi(G_{r_n})\le\frac83\rho+\frac43\beta$
-- statement:
--   Let $\mathcal Y$ be finite, let $n\ge1$ and $r_n=1/\sqrt{32n}$. If an $n$-sample algorithm is $(\beta,\rho)$-valid, then
--
--   $$
--   \Phi(G_{r_n})\le\frac83\rho+\frac43\beta .
--   $$
--
--   The seed space of the algorithm is arbitrary. This reduces the lower bound for algorithms to a statement about selector laws on one graph.
--
--   Differences from the source:
--   - encoding: a known family P = {P1, …, PM} of distinct distributions on a finite set Z → an `Experiment ι Z`: an injective table of probability vectors over a finite index type, with Z in `Type` and M = `Fintype.card ι`; reason: models are named by index; the reused Bhattacharyya coefficient takes a type in `Type`, which loses no finite Z
--   - encoding: probabilities over S, S′ ∼ Pⁿ and the seed R → finite sums over samples `Fin n → Z` of products of table entries times seed-measure terms `μ.real`; reason: the data side is finite; the same numbers
--   - encoding: A : Zⁿ × R → Y measurable in its seed → `A : (Fin n → Z) → Ω → Y` with every `{ω | A x ω = y}` measurable, on an arbitrary probability space; reason: on a finite Y this is measurability in the seed
--   - encoding: the profile as a minimum over selector laws → `IsLeast` of the set of objective values at laws in `stdSimplex ℝ (ι → Y)`, with `DecidableEq ι` for the finite function type; reason: the page says all finite minima are attained; no instance changes
--   - encoding: a family P = {P1, …, PM} → `[Nonempty ι]`, M ≥ 1; reason: with no model the maximum over P in Φ is undefined (Lean's empty supremum is 0) and validity is vacuous for negative β, ρ; this only excludes the degenerate empty family
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Lemma 3.3, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_weakGraph
import Definitions.Def_ReplicableDecisions_profileValues

open MeasureTheory

namespace ReplicableDecisions

/-- **Lemma 3.3 (Canonical-output reduction).** Chen, *Replicable Decisions in Finite Experiments*, STOC
2027 submission (sha256 52d181db…), Lemma 3.3, p.12 (PDF p.14): "Let Y be finite, n ≥ 1, and
r_n = 1/√(32n). If an n-sample algorithm is (β, ρ)-valid, then Φ(G_{r_n}) ≤ (8/3)ρ + (4/3)β."

**Formalization Note.** `Φ(G)` is read as the least element of `phiValues G Γ`, so its attainment is
part of the conclusion. The seed space is arbitrary. -/
theorem lemma_3_3 {ι : Type*} {Z : Type} {Y : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Z] [Fintype Y] (E : Experiment ι Z) (Γ : ι → Set Y) (hΓ : ∀ i, (Γ i).Nonempty)
    {β ρ : ℝ} {n : ℕ} (hn : 1 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : (Fin n → Z) → Ω → Y) (hA : IsValid E Γ β ρ μ A) :
    ∃ v, IsLeast (phiValues (weakGraph E (1 / Real.sqrt (32 * n))) Γ) v ∧
      v ≤ 8 / 3 * ρ + 4 / 3 * β := by sorry

end ReplicableDecisions
