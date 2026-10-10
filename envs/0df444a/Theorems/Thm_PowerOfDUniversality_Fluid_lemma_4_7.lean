-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_lemma_4_7
-- name    : PowerOfDUniversality.Fluid.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:56.070109+00:00
-- url     : https://prove2.me/theorems/42d8c398-3653-4e98-865e-7d8b43d937e8
-- title:
--   Lemma 4.7 — tightness in ℓ¹ ⇔ tightness in the product topology plus vanishing tails (4.23)
-- statement:
--   Let $\{\mathbf X^N\}_{N\ge1}$ be a sequence of random variables with values in $\mathcal S$. The following are equivalent:
--   1. $\{\mathbf X^N\}$ is tight with respect to the product topology, and for all $\varepsilon>0$
--   $$\lim_{k\to\infty}\ \limsup_{N\to\infty}\ \mathbb P\Big(\sum_{i\ge k}X^N_i>\varepsilon\Big)=0; \tag{4.23}$$
--   2. $\{\mathbf X^N\}$ is tight with respect to the $\ell_1$ topology.
--
--   Tightness with respect to a topology means: for every $\varepsilon>0$ there is a compact set $K\subseteq\mathcal S$ (compact in that topology) with $\mathbb P(\mathbf X^N\notin K)\le\varepsilon$ for all $N$. The lemma reduces $\ell_1$-tightness, needed for the fluid limit in $\ell_1$, to coordinatewise tightness and a uniform tail bound.
--
--   **Formalization Note** The random variables live on one probability space and are measurable for the product σ-algebra of $\mathbb R^{\mathbb N}$. The statement is for a general buffer $b\ge1$ (the lemma states no restriction; for finite $b$ both sides hold trivially). Compactness in $\ell_1$ is compactness of the corresponding subset of the Banach space $\ell^1$.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 21–22, Lemma 4.7, (4.23)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Lemma 4.7** (p. 21, criterion for `ℓ¹`-tightness). Let `X^N`, `N = 0, 1, …`, be random
variables in `𝕊` (buffer `b ≥ 1`). The following are equivalent:

1. `{X^N}` is tight with respect to the product topology (for every `ε > 0` some `K ⊆ 𝕊`,
   compact in the product topology of `ℝ^ℕ`, has `P(X^N ∉ K) ≤ ε` for all `N`), and for all
   `ε > 0`, `lim_{k→∞} limsup_{N→∞} P(∑_{i≥k} X^N_i > ε) = 0` (4.23);
2. `{X^N}` is tight with respect to the `ℓ¹` topology (the same with `K` compact in `ℓ¹`). -/
theorem lemma_4_7 (b : ℕ∞) (hb : 1 ≤ b)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ → ℝ) (hXm : ∀ N, Measurable (X N)) (hXS : ∀ N ω, X N ω ∈ FluidSpace b) :
    ((∀ ε : ℝ, 0 < ε → ∃ K ⊆ FluidSpace b, IsCompact K ∧
        ∀ N, P {ω | X N ω ∉ K} ≤ ENNReal.ofReal ε) ∧
      ∀ ε : ℝ, 0 < ε → Tendsto (fun k : ℕ =>
        limsup (fun N => P {ω | ε < ∑' i : ℕ, X N ω (k + i)}) atTop) atTop (𝓝 0)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ K ⊆ FluidSpace b,
        IsCompact {x : lp (fun _ : ℕ => ℝ) 1 | (x : ℕ → ℝ) ∈ K} ∧
        ∀ N, P {ω | X N ω ∉ K} ≤ ENNReal.ofReal ε) := by sorry

end PowerOfDUniversality.Fluid
