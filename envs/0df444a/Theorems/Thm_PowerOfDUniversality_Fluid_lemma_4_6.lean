-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_lemma_4_6
-- name    : PowerOfDUniversality.Fluid.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:31.293394+00:00
-- url     : https://prove2.me/theorems/658b51ce-30b9-4dbf-9217-85ef305a04ea
-- title:
--   Lemma 4.6 — K ⊆ 𝕊 is relatively compact in ℓ¹ iff lim_k sup_{x∈K} Σ_{i≥k} x_i = 0 (b = ∞)
-- statement:
--   Let the buffer be infinite, $b=\infty$, and let $\mathcal S$ carry the $\ell_1$ topology. A set $K\subseteq\mathcal S$ is relatively compact in $\mathcal S$ if and only if its tails are uniformly small:
--   $$\lim_{k\to\infty}\ \sup_{\mathbf x\in K}\ \sum_{i=k}^{\infty}x_i=0. \tag{4.19}$$
--
--   This characterization of compact sets is what turns tail estimates into $\ell_1$-tightness of the fluid-scaled occupancy processes.
--
--   **Formalization Note** "Relatively compact in $\mathcal S$" is the compactness of the closure of $K$ inside $\mathcal S\subseteq\ell^1$ (subspace topology). The supremum of the tails is taken in $[0,\infty]$, so the empty set and unbounded tails need no special case.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 20–21, Lemma 4.6, (4.19)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Lemma 4.6** (p. 20, compact subsets of `𝕊`). Assume `b = ∞`. A set `K ⊆ 𝕊` is relatively
compact in `𝕊` with respect to the `ℓ¹` topology (its closure in `𝕊 ⊆ ℓ¹` is compact) if and only if
`lim_{k→∞} sup_{x ∈ K} ∑_{i=k}^{∞} x_i = 0` (4.19). -/
theorem lemma_4_6 (K : Set (ℕ → ℝ)) (hK : K ⊆ FluidSpace ⊤) :
    IsCompact (closure {x : FluidSpaceL1 ⊤ |
        ((x : lp (fun _ : ℕ => ℝ) 1) : ℕ → ℝ) ∈ K}) ↔
      Tendsto (fun k : ℕ => ⨆ x ∈ K, ∑' i : ℕ, ENNReal.ofReal (x (k + i))) atTop (𝓝 0) := by sorry

end PowerOfDUniversality.Fluid
