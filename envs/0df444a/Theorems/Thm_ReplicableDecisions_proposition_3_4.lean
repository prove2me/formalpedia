-- Prove2me | Theorems.Thm_ReplicableDecisions_proposition_3_4
-- name    : ReplicableDecisions.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:07:33.053133+00:00
-- url     : https://prove2.me/theorems/78005a96-6a4b-4406-a187-8062e0c05550
-- title:
--   Proposition 3.4 — chain obstruction: $1\le2(\beta+\rho)+\frac83k\rho$
-- statement:
--   Let $\mathcal Y$ be finite, $n\ge1$, $r_n=1/\sqrt{32n}$, and suppose that an $n$-sample algorithm is $(\beta,\rho)$-valid. Then any path $P_0,\dots,P_D$ in $G_{r_n}$ with $\Gamma(P_0)\cap\Gamma(P_D)=\emptyset$ satisfies, for $k=\lceil D/2\rceil$,
--
--   $$
--   1\le2(\beta+\rho)+\frac83k\rho .
--   $$
--
--   In particular, for two outputs and $\rho>0$, a finite $D_{r_n}$ implies
--
--   $$
--   k_{r_n}\ge\frac{3(1-2\beta-2\rho)}{8\rho}.
--   $$
--
--   This is the converse of the mission's goal: chains of few hops between opposite forced answers are incompatible with validity.
--
--   Differences from the source:
--   - encoding: a known family P = {P1, …, PM} of distinct distributions on a finite set Z → an `Experiment ι Z`: an injective table of probability vectors over a finite index type, with Z in `Type` and M = `Fintype.card ι`; reason: models are named by index; the reused Bhattacharyya coefficient takes a type in `Type`, which loses no finite Z
--   - encoding: probabilities over S, S′ ∼ Pⁿ and the seed R → finite sums over samples `Fin n → Z` of products of table entries times seed-measure terms `μ.real`; reason: the data side is finite; the same numbers
--   - encoding: A : Zⁿ × R → Y measurable in its seed → `A : (Fin n → Z) → Ω → Y` with every `{ω | A x ω = y}` measurable, on an arbitrary probability space; reason: on a finite Y this is measurability in the seed
--   - encoding: a path P0, …, PD in G_{r_n} → a Mathlib `Walk` with `IsPath`, D its length; reason: the same object
--   - encoding: two outputs, D_{r_n} = dist(A0, A1) → `Nat.card Y = 2`, and `forcedDist` for any two distinct outputs y₀, y₁; reason: names the two outputs of an abstract two-element type; `Bool` is the case y₀ = false, y₁ = true
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Proposition 3.4, (3.3), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_weakGraph
import Definitions.Def_ReplicableDecisions_forcedDist

open MeasureTheory

namespace ReplicableDecisions

/-- **Proposition 3.4 (A chain obstruction with separate accuracy dependence).** Chen, *Replicable
Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), Proposition 3.4, p.13
(PDF p.15). Under the assumptions of Lemma 3.3: a path `P₀, …, P_D` in `G_{r_n}` with
`Γ(P₀) ∩ Γ(P_D) = ∅` has `1 ≤ 2(β + ρ) + (8/3)kρ`, `k = ⌈D/2⌉`, (3.3). For two outputs and `ρ > 0`, a
finite `D_{r_n}` has `k_{r_n} ≥ 3(1 − 2β − 2ρ)/(8ρ)`.

**Formalization Note.** A path is a Mathlib `Walk` with `IsPath`, and `D` is its length. "Two outputs"
is `Nat.card Y = 2`, with `y₀ ≠ y₁` naming them. -/
theorem proposition_3_4 {ι : Type*} {Z : Type} {Y : Type*} [Fintype ι]
    [Fintype Z] [Fintype Y] (E : Experiment ι Z) (Γ : ι → Set Y) (hΓ : ∀ i, (Γ i).Nonempty)
    {β ρ : ℝ} {n : ℕ} (hn : 1 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : (Fin n → Z) → Ω → Y) (hA : IsValid E Γ β ρ μ A) :
    (∀ (a b : ι) (p : (weakGraph E (1 / Real.sqrt (32 * n))).Walk a b), p.IsPath →
        Γ a ∩ Γ b = ∅ →
        1 ≤ 2 * (β + ρ) + 8 / 3 * (⌈(p.length : ℝ) / 2⌉₊ : ℝ) * ρ) ∧
      (Nat.card Y = 2 → 0 < ρ → ∀ y₀ y₁ : Y, y₀ ≠ y₁ → ∀ D : ℕ,
        forcedDist (weakGraph E (1 / Real.sqrt (32 * n))) Γ y₀ y₁ = D →
        3 * (1 - 2 * β - 2 * ρ) / (8 * ρ) ≤ (⌈(D : ℝ) / 2⌉₊ : ℝ)) := by sorry

end ReplicableDecisions
