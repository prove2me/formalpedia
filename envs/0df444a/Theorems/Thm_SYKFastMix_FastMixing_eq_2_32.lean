-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_eq_2_32
-- name    : SYKFastMix.FastMixing.eq_2_32
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:02:30.451792+00:00
-- url     : https://prove2.me/theorems/9d3415f0-d695-41c5-99fc-36d7f03d2de5
-- title:
--   Gap-to-trace-norm contraction estimate (2.32)
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on a nonempty finite-dimensional Hilbert space, let the jump couplings be Hermitian, and let $\beta\ge 0$. Assume the discriminant of the associated Gibbs sampler has spectral gap $\lambda>0$ in the full-space sense encoded by `HasGap`. Then, for every $\tau\ge0$ and every density matrix $X$,
--
--   $$
--   \left\|e^{\tau\mathcal L}(X)-\rho_\beta\right\|_1\le e^{-\lambda\tau}\sqrt{d}\,e^{\beta\lVert H\rVert},
--   $$
--
--   where $d$ is the Hilbert-space dimension. This is the trace-norm contraction estimate used to derive the explicit worst-case mixing time.
-- source:
--   Cai, Zhan, Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1050.pdf, Section 2, p.12, Equation (2.32)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem eq_2_32 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (hH : H.IsHermitian)
    (hγ : ∀ i, (γ i).IsHermitian) (β rate : ℝ) (hβ : 0 ≤ β) (hrate : 0 < rate)
    (hgap : HasGap (discriminant H γ β) (gibbsRoot H β) rate) :
  ∀ τ : ℝ, 0 ≤ τ → ∀ X, IsDensity X →
    traceNorm (evolve (lindblad H γ β) τ X - gibbs H β) ≤
      Real.exp (-rate * τ) * Real.sqrt (Fintype.card ι : ℝ) * Real.exp (β * SYKEdge.opNorm H) := by sorry

end SYKFastMix.FastMixing
