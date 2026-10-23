-- Prove2me | Theorems.Thm_ParallelSU2_Reduction_parallel_su2_estimation
-- name    : ParallelSU2.Reduction.parallel_su2_estimation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:22.038575+00:00
-- url     : https://prove2.me/theorems/cce5679d-4504-4fe9-b5ec-f5e81ba87c2e
-- title:
--   §3, eq. (14) and p. 8 — with a reference, n = 2d − 1 uses of SU(2) reach error sin²(π/(2d+2)) exactly, and (2d−1)²·sin²(π/(2d+2)) → π²
-- statement:
--   Throughout, $\mu$ is the invariant probability measure on $\mathrm{SU}(2)$ (a left- and right-invariant Borel probability measure). The cost is $d(g,\hat g)=1-|\operatorname{Tr}(g^{-1}\hat g)/2|^2$. For $n=2d-1$ uses of an unknown $g$, the state lives on $\bigoplus_{k=1}^d\mathcal H_{2k}\otimes\mathcal H_{2k,R}$, where $g$ acts as $U_g=\bigoplus_kV^{2k}_g\otimes I$, the input is $x_{\vec x}=\bigoplus_kx_kx^{2k}_E$ with $\sum|x_k|^2=1$, and the measurement is $M^T(d\hat g)=U_{\hat g}\big(\sum_{k,l}t_{k,l}|(2k)x^{2k}_E\rangle\langle(2l)x^{2l}_E|\big)U_{\hat g}^\dagger\mu(d\hat g)$. The following hold.
--
--   1. For every $d$ there is a spin family: continuous unitary irreducible representations $V^2,\dots,V^{2d}$ of dimensions $2,\dots,2d$ with the Weyl characters.
--   2. For every $d$, every spin family, every unit $x\in\mathbb C^d$ and every Hermitian $T\ge0$ with $t_{k,k}=1$, $M^T$ is a POVM (a density measurement with reference measure $\mu$), and for every true $g$ its error is exactly
--   $$\mathcal D_g(M^T,x)=\frac12\sum_k|x_k|^2t_{k,k}-\frac14\sum_{k=1}^{d-1}\operatorname{Re}\big(\overline{x_k}x_{k+1}t_{k,k+1}+\overline{x_{k+1}}x_kt_{k+1,k}\big)\ \ge\ v(x)=\frac12\Big(1-\sum_{k=1}^{d-1}|x_k||x_{k+1}|\Big),$$
--   with equality for the phase-aligned $T$.
--   3. For $d\ge1$ the least value of $v(x)$ over unit $x\in\mathbb C^d$ is
--   $$\mathcal D^{d-1}_{\rm opt}=\sin^2\frac{\pi}{2d+2}.$$
--   4. $$\lim_{d\to\infty}(2d-1)^2\sin^2\frac{\pi}{2d+2}=\pi^2,$$ that is, $n^2\cdot$(error) $\to\pi^2$.
--
--   This is the paper's reduction of SU(2) estimation to phase estimation, with the conclusion "the estimation error is equal to $\pi^2/n^2$ asymptotically" in exact form.
--
--   **Corrected statement.** (14) and (9) are used with the corrected conjugation (see the milestone for eq. (14)); "$\cong$" is replaced by the exact optimum and the limit.
--
--   **Formalization Note** $\mathrm{SU}(2)$ is `Matrix.specialUnitaryGroup (Fin 2) ℂ` with its subspace topology. The pinned Mathlib provides no topological-group, compactness or measurable-space instance on it, so `IsTopologicalGroup`, `CompactSpace`, a `MeasurableSpace` with `BorelSpace` are taken as instance hypotheses (all true for the actual SU(2)), and the Haar measure is any probability measure `dg` that is left and right invariant. The irreps are indexed $k=0,\dots,d-1$ for $\mathcal H_2,\dots,\mathcal H_{2d}$; the Weyl-character hypothesis is a true property of such irreps, and clause 1 rules out an empty family of irreps. The error is pointwise in $g$, not Haar-averaged, and the optimum is an attained least element, not an infimum.
-- source:
--   Hayashi, Parallel Treatment of Estimation of SU(2) and Phase Estimation, arXiv:quant-ph/0407053v3, p. 8, eq. (14) and the paragraph after it ("Thus, the optimal error of this estimation method coincides with D^{m−1}_opt … π²/n²"); abstract and p. 3

import Mathlib
import Definitions.Def_ParallelSU2_Reduction_Setting
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace ParallelSU2.Reduction

/-- Hayashi §3, p. 8, eq. (14) and the sentence after it, exact form, for `n = 2d − 1` uses with a
reference system: (1) the irreducible spaces `H_2, …, H_{2d}` exist; (2) for every unit `x` and
every Hermitian `T ≥ 0` with unit diagonal, `M^T_{2d−1}` is a POVM whose error at every true `g` is
the corrected (14), at least `v(x) = ½(1 − ∑|x_k||x_{k+1}|)`, with equality for the phase-aligned
`T`; (3) the least value of `v` over unit inputs is `sin²(π/(2d+2))` (`D^{d−1}_opt`);
(4) `(2d − 1)² sin²(π/(2d+2)) → π²`. -/
theorem parallel_su2_estimation
    [IsTopologicalGroup SU2] [CompactSpace SU2] [MeasurableSpace SU2] [BorelSpace SU2]
    (dg : Measure SU2) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg] :
    (∀ d : ℕ, ∃ D : Fin d → QAlgorithms.Papers.Independent.Next46.P36.BasedIrrep SU2,
      IsSpinFamily D) ∧
    (∀ (d : ℕ) (D : Fin d → QAlgorithms.Papers.Independent.Next46.P36.BasedIrrep SU2),
      IsSpinFamily D →
      ∀ x : Fin d → ℂ, ∑ k, Complex.normSq (x k) = 1 →
      ∀ T : Matrix (Fin d) (Fin d) ℂ, T.PosSemidef → (∀ k, T k k = 1) →
      ∃ M : QAlgorithms.Measurements.DensityPOVM
          (QAlgorithms.Papers.Independent.Next46.P36.CanonicalIndex D) SU2,
        M.reference = dg ∧
        (∀ h, M.density h = QAlgorithms.conjSuperop
          (QAlgorithms.Papers.Independent.Next46.P36.canonicalAction D h) (hayashiSeed D T)) ∧
        ∀ g : SU2,
          pointwiseRisk (QAlgorithms.Papers.Independent.Next46.P36.canonicalAction D)
              QAlgorithms.Papers.Independent.Next46.P36.bellCost
              (QAlgorithms.pureDensity
                (QAlgorithms.Papers.Independent.Next46.P36.canonicalInput D x (fun _ => 1))) M g =
              hayashiError x T ∧
          methodValue x ≤ hayashiError x T ∧
          (T = phaseAligned x → hayashiError x T = methodValue x)) ∧
    (∀ d : ℕ, 1 ≤ d →
      IsLeast {r : ℝ | ∃ x : Fin d → ℂ, ∑ k, Complex.normSq (x k) = 1 ∧ r = methodValue x}
        (Real.sin (Real.pi / (2 * (d : ℝ) + 2)) ^ 2)) ∧
    Tendsto (fun d : ℕ => (2 * (d : ℝ) - 1) ^ 2 * Real.sin (Real.pi / (2 * (d : ℝ) + 2)) ^ 2)
      atTop (𝓝 (Real.pi ^ 2)) := by sorry

end ParallelSU2.Reduction
