-- Prove2me | Theorems.Thm_ParallelSU2_Reduction_single_character_integral
-- name    : ParallelSU2.Reduction.single_character_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:18.548364+00:00
-- url     : https://prove2.me/theorems/41f33c9a-2f76-4833-a651-81a8a147bc70
-- title:
--   Eq. (12) — ∫ d(I, ĝ) |Tr V^j_ĝ|² µ(dĝ) = 3/4 for j = 1 and 1/2 for j ≥ 2
-- statement:
--   Throughout, $\mu$ is the invariant probability measure on $\mathrm{SU}(2)$ (a left- and right-invariant Borel probability measure). Let $d(I,\hat g)=1-|\operatorname{Tr}\hat g/2|^2$ and let $\chi_j$ be the character of the $j$-dimensional irreducible representation, $\chi_j(\hat g)=U_{j-1}(\operatorname{Re}\operatorname{Tr}\hat g/2)$. For every $j\ge1$,
--   $$\int_{\mathrm{SU}(2)}d(I,\hat g)\,|\chi_j(\hat g)|^2\,\mu(d\hat g)=\begin{cases}3/4,& j=1,\\ 1/2,& j\ge2.\end{cases}$$
--
--   This is the error of the single-irrep scheme $M_{j,E}$: using one irreducible space, however large, the error does not fall below $1/2$, which is why the paper correlates several irreducible spaces.
--
--   **Formalization Note** $\mathrm{SU}(2)$ is `Matrix.specialUnitaryGroup (Fin 2) ℂ` with its subspace topology. The pinned Mathlib provides no topological-group, compactness or measurable-space instance on it, so `IsTopologicalGroup`, `CompactSpace`, a `MeasurableSpace` with `BorelSpace` are taken as instance hypotheses (all true for the actual SU(2)), and the Haar measure is any probability measure `dg` that is left and right invariant. The characters are real, so $|\chi_j|^2=\chi_j^2$. Section 4 of the paper (p. 9) prints the value $1/2$ for the $j=1$ integral; the integral it writes evaluates to $3/4$, the value of (12).
-- source:
--   Hayashi, Parallel Treatment of Estimation of SU(2) and Phase Estimation, arXiv:quant-ph/0407053v3, p. 7, eq. (12) (final equality; derivation p. 9)

import Mathlib
import Definitions.Def_ParallelSU2_Reduction_Setting
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace ParallelSU2.Reduction

/-- Hayashi p. 7, eq. (12), final equality: `∫ d(I, ĝ) |Tr V^j_ĝ|² µ(dĝ) = 3/4` for `j = 1` and
`1/2` for `j ≥ 2`, with `d(I, ĝ) = 1 − |Tr ĝ / 2|²` (`P36.bellCost ĝ 1`) and the Weyl character
(real-valued, so `|χ|² = χ²`). -/
theorem single_character_integral
    [IsTopologicalGroup SU2] [CompactSpace SU2] [MeasurableSpace SU2] [BorelSpace SU2]
    (dg : Measure SU2) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (j : ℕ) (hj : 1 ≤ j) :
    ∫ g, QAlgorithms.Papers.Independent.Next46.P36.bellCost g 1 * weylCharacter j g ^ 2 ∂dg =
      if j = 1 then (3 / 4 : ℝ) else 1 / 2 := by sorry

end ParallelSU2.Reduction
