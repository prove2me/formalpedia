-- Prove2me | Theorems.Thm_ParallelSU2_Reduction_character_integral
-- name    : ParallelSU2.Reduction.character_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:30.499993+00:00
-- url     : https://prove2.me/theorems/890932b5-7011-4f68-994c-137fb879c75c
-- title:
--   Eq. (13) — ∫ d(I, ĝ) χ_2k(ĝ) χ_2l(ĝ) µ(dĝ) = ½δ_kl − ¼δ_{k,l−1} − ¼δ_{k−1,l}
-- statement:
--   Throughout, $\mu$ is the invariant probability measure on $\mathrm{SU}(2)$ (a left- and right-invariant Borel probability measure). With $d(I,\hat g)=1-|\operatorname{Tr}\hat g/2|^2$ and $\chi_j$ the character of the $j$-dimensional irreducible representation, for all integers $k,l\ge1$,
--   $$\int_{\mathrm{SU}(2)}d(I,\hat g)\,\chi_{2k}(\hat g)\,\overline{\chi_{2l}(\hat g)}\,\mu(d\hat g)=\tfrac12\delta_{k,l}-\tfrac14\delta_{k,l-1}-\tfrac14\delta_{k-1,l}.$$
--
--   The right-hand side is exactly the kernel of the phase-estimation identity (7). This is the relation that reduces estimation of an SU(2) action on $\bigoplus_k\mathcal H_{2k}\otimes\mathcal H_{2k,R}$ to Bužek's phase-estimation problem.
--
--   **Formalization Note** $\mathrm{SU}(2)$ is `Matrix.specialUnitaryGroup (Fin 2) ℂ` with its subspace topology. The pinned Mathlib provides no topological-group, compactness or measurable-space instance on it, so `IsTopologicalGroup`, `CompactSpace`, a `MeasurableSpace` with `BorelSpace` are taken as instance hypotheses (all true for the actual SU(2)), and the Haar measure is any probability measure `dg` that is left and right invariant. The characters are real, so the conjugation is omitted. The paper writes $d(g,\hat g)$ and $\operatorname{Tr}V_{\hat g}$ after its change of variables; the statement uses $d(I,\hat g)$ as in its derivation on p. 10.
-- source:
--   Hayashi, Parallel Treatment of Estimation of SU(2) and Phase Estimation, arXiv:quant-ph/0407053v3, p. 8, eq. (13) (outer equality; derived p. 10)

import Mathlib
import Definitions.Def_ParallelSU2_Reduction_Setting
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace ParallelSU2.Reduction

/-- Hayashi p. 8, eq. (13), outer equality (derived on p. 10):
`∫ d(I, ĝ) Tr V^{2k}_ĝ (Tr V^{2l}_ĝ)^* µ(dĝ) = ½δ_{k,l} − ¼δ_{k,l−1} − ¼δ_{k−1,l}` for `k, l ≥ 1`.
The Weyl characters are real, so no conjugation is written. -/
theorem character_integral
    [IsTopologicalGroup SU2] [CompactSpace SU2] [MeasurableSpace SU2] [BorelSpace SU2]
    (dg : Measure SU2) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ∫ g, QAlgorithms.Papers.Independent.Next46.P36.bellCost g 1 *
        weylCharacter (2 * k) g * weylCharacter (2 * l) g ∂dg =
      (if k = l then (1 / 2 : ℝ) else 0) - (if k + 1 = l then (1 / 4 : ℝ) else 0) -
        (if l + 1 = k then (1 / 4 : ℝ) else 0) := by sorry

end ParallelSU2.Reduction
