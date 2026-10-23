-- Prove2me | Theorems.Thm_ParallelSU2_Reduction_error_formula
-- name    : ParallelSU2.Reduction.error_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:13.508475+00:00
-- url     : https://prove2.me/theorems/ea698f83-6f53-4bbb-a8e2-29e118813ead
-- title:
--   Eq. (14), corrected — error of M^T at every g is ½Σ|x_k|²t_kk − ¼ΣRe(x̄_k x_{k+1} t_{k,k+1} + c.c.) ≥ ½(1 − Σ|x_k||x_{k+1}|), equality for (9)
-- statement:
--   Throughout, $\mu$ is the invariant probability measure on $\mathrm{SU}(2)$ (a left- and right-invariant Borel probability measure). Let $D_0,\dots,D_{d-1}$ be a spin family, $x\in\mathbb C^d$ with $\sum_k|x_k|^2=1$ (condition (1)), and $T$ a $d\times d$ Hermitian positive semidefinite matrix with unit diagonal. Let $M$ be the measurement with reference measure $\mu$ and density $M(\hat g)=U_{\hat g}\Xi_TU_{\hat g}^\dagger$, and let the input be $\rho=|x_{\vec x}\rangle\langle x_{\vec x}|$ with $x_{\vec x}=\bigoplus_kx_kx^{2k}_E$. Then for every true $g\in\mathrm{SU}(2)$, with $d(g,\hat g)=1-|\operatorname{Tr}(g^{-1}\hat g)/2|^2$,
--   $$\mathcal D_g=\int d(g,\hat g)\operatorname{Tr}M(\hat g)U_g\rho U_g^\dagger\,\mu(d\hat g)=\frac12\sum_{k=1}^d|x_k|^2t_{k,k}-\frac14\sum_{k=1}^{d-1}\operatorname{Re}\big(\overline{x_k}x_{k+1}t_{k,k+1}+\overline{x_{k+1}}x_kt_{k+1,k}\big),$$
--   this value is at least
--   $$v(x)=\frac12\Big(1-\sum_{k=1}^{d-1}|x_k||x_{k+1}|\Big),$$
--   and it equals $v(x)$ when $T$ is the phase-aligned matrix $t_{k,l}=\phi(x_k)\overline{\phi(x_l)}$, $\phi(z)=z/|z|$, $\phi(0)=1$.
--
--   This is the reduction: the SU(2) error of $M^T$ equals the phase-estimation error (8) of the same coefficients.
--
--   **Corrected statement.** The paper prints $\overline{x_{k-1}}x_kt_{k,k-1}+\overline{x_k}x_{k-1}t_{k-1,k}$ and, in (9), $t_{k,k+1}=\overline{x_k}x_{k+1}/|x_kx_{k+1}|$. Since $\operatorname{Tr}M\rho$ expands as $\sum t_{k,l}\overline{x_k}x_l\cdots$, the indices of $t$ are swapped; with the printed $T_x$ the bound is not attained for complex $x$ (e.g. $d=2$, $x=(1,i)/\sqrt2$: $3/4$ instead of $1/4$). The statement uses the corrected pairing and the conjugate phase matrix.
--
--   **Formalization Note** $\mathrm{SU}(2)$ is `Matrix.specialUnitaryGroup (Fin 2) ℂ` with its subspace topology. The pinned Mathlib provides no topological-group, compactness or measurable-space instance on it, so `IsTopologicalGroup`, `CompactSpace`, a `MeasurableSpace` with `BorelSpace` are taken as instance hypotheses (all true for the actual SU(2)), and the Haar measure is any probability measure `dg` that is left and right invariant. The cost is the published `bellCost` (estimate first, truth second), the error is pointwise in $g$ (not Haar-averaged), the trace is $\operatorname{Re}\operatorname{Tr}$ (`effectProb`), and the statement holds for every density measurement $M$ with these data (one exists by the normalization milestone).
-- source:
--   Hayashi, Parallel Treatment of Estimation of SU(2) and Phase Estimation, arXiv:quant-ph/0407053v3, p. 8, eq. (14) and "The equality holds when matrix T = (t_k,l) satisfies (9)" (corrected conjugation; (9) p. 5)

import Mathlib
import Definitions.Def_ParallelSU2_Reduction_Setting
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace ParallelSU2.Reduction

/-- Hayashi p. 8, eq. (14), corrected conjugation: for a unit coefficient vector `x` and a
Hermitian `T ≥ 0` with unit diagonal, the covariant measurement `M^T_{2d−1}` applied to the input
`⊕_k x_k x^{2k}_E` has, at every true `g`, error exactly
`½∑|x_k|² t_{k,k} − ¼∑(x̄_k x_{k+1} t_{k,k+1} + x̄_{k+1} x_k t_{k+1,k})`; this is at least
`½(1 − ∑|x_k||x_{k+1}|)`, with equality for the phase-aligned `T`. -/
theorem error_formula
    [IsTopologicalGroup SU2] [CompactSpace SU2] [MeasurableSpace SU2] [BorelSpace SU2]
    (dg : Measure SU2) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    {d : ℕ} (D : Fin d → QAlgorithms.Papers.Independent.Next46.P36.BasedIrrep SU2)
    (hD : IsSpinFamily D)
    (x : Fin d → ℂ) (hx : ∑ k, Complex.normSq (x k) = 1)
    (T : Matrix (Fin d) (Fin d) ℂ) (hT : T.PosSemidef) (hdiag : ∀ k, T k k = 1)
    (M : QAlgorithms.Measurements.DensityPOVM
      (QAlgorithms.Papers.Independent.Next46.P36.CanonicalIndex D) SU2)
    (hMref : M.reference = dg)
    (hMden : ∀ h, M.density h = QAlgorithms.conjSuperop
      (QAlgorithms.Papers.Independent.Next46.P36.canonicalAction D h) (hayashiSeed D T))
    (g : SU2) :
    pointwiseRisk (QAlgorithms.Papers.Independent.Next46.P36.canonicalAction D)
        QAlgorithms.Papers.Independent.Next46.P36.bellCost
        (QAlgorithms.pureDensity
          (QAlgorithms.Papers.Independent.Next46.P36.canonicalInput D x (fun _ => 1))) M g =
        hayashiError x T ∧
      methodValue x ≤ hayashiError x T ∧
      (T = phaseAligned x → hayashiError x T = methodValue x) := by sorry

end ParallelSU2.Reduction
