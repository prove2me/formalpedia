-- Prove2me | Theorems.Thm_ParallelSU2_Reduction_seed_normalized
-- name    : ParallelSU2.Reduction.seed_normalized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:14.487447+00:00
-- url     : https://prove2.me/theorems/e30c6ef2-daa8-4834-94c0-bbf94b882186
-- title:
--   p. 8 — for Hermitian T ≥ 0 with t_kk = 1, the total integral of M^T_{2d−1} is the identity (M^T is a POVM)
-- statement:
--   Throughout, $\mu$ is the invariant probability measure on $\mathrm{SU}(2)$ (a left- and right-invariant Borel probability measure). Let $D_0,\dots,D_{d-1}$ be a spin family (irreducible representations of dimensions $2,4,\dots,2d$ with the Weyl characters), acting by $U_g=\bigoplus_k D_k(g)\otimes I$ on $\bigoplus_k\mathcal H_{2k}\otimes\mathcal H_{2k,R}$. Let $T=(t_{k,l})$ be a $d\times d$ Hermitian positive semidefinite matrix with $t_{k,k}=1$ for every $k$ (condition (6)), and $\Xi_T=\sum_{k,l}t_{k,l}|(2k)x^{2k}_E\rangle\langle(2l)x^{2l}_E|$. Then $\Xi_T\ge0$, the map $\hat g\mapsto U_{\hat g}\Xi_TU_{\hat g}^\dagger$ is continuous and integrable, and
--   $$\int_{\mathrm{SU}(2)}U_{\hat g}\,\Xi_T\,U_{\hat g}^\dagger\,\mu(d\hat g)=I .$$
--
--   Hence $M^T_{2d-1}(d\hat g)=U_{\hat g}\Xi_TU_{\hat g}^\dagger\mu(d\hat g)$ is a covariant POVM.
--
--   **Formalization Note** $\mathrm{SU}(2)$ is `Matrix.specialUnitaryGroup (Fin 2) ℂ` with its subspace topology. The pinned Mathlib provides no topological-group, compactness or measurable-space instance on it, so `IsTopologicalGroup`, `CompactSpace`, a `MeasurableSpace` with `BorelSpace` are taken as instance hypotheses (all true for the actual SU(2)), and the Haar measure is any probability measure `dg` that is left and right invariant. The conclusion is the published predicate `NormalizedSeed` (positive semidefinite seed, continuous and integrable orbit, integral one, the Bochner integral taken in the $L^2$-operator norm).
-- source:
--   Hayashi, Parallel Treatment of Estimation of SU(2) and Phase Estimation, arXiv:quant-ph/0407053v3, p. 8, definition of M^T_{2d−1} and "Using Schur's lemma and condition (6) …"

import Mathlib
import Definitions.Def_ParallelSU2_Reduction_Setting
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace ParallelSU2.Reduction

/-- Hayashi p. 8: for a Hermitian `T ≥ 0` with `t_{k,k} = 1` (condition (6)), the covariant
density `ĝ ↦ U_ĝ (∑ t_{k,l} |(2k)x^{2k}_E⟩⟨(2l)x^{2l}_E|) U_ĝ^†` is a legal seed: positive
semidefinite, continuous and integrable in `ĝ`, with total integral the identity. -/
theorem seed_normalized
    [IsTopologicalGroup SU2] [CompactSpace SU2] [MeasurableSpace SU2] [BorelSpace SU2]
    (dg : Measure SU2) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    {d : ℕ} (D : Fin d → QAlgorithms.Papers.Independent.Next46.P36.BasedIrrep SU2)
    (hD : IsSpinFamily D)
    (T : Matrix (Fin d) (Fin d) ℂ) (hT : T.PosSemidef) (hdiag : ∀ k, T k k = 1) :
    QAlgorithms.Papers.Independent.Next46.P36.NormalizedSeed D dg (hayashiSeed D T) := by sorry

end ParallelSU2.Reduction
