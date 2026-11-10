-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_eq_2_33
-- name    : SYKFastMix.FastMixing.eq_2_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:13.247604+00:00
-- url     : https://prove2.me/theorems/531a969d-955b-4cf3-b16e-b17da6666caf
-- title:
--   Eq. (2.33) — full trace-norm convergence and worst-case mixing
-- statement:
--   Let $H$ be Hermitian on a nonzero $d$-dimensional complex Hilbert space, let $\gamma_i$ be Hermitian coupling operators, and form the actual Gibbs sampler and discriminant of (2.20)–(2.28) at $\beta\ge0$. Suppose its discriminant has gap at least $\lambda>0$ on the entire complement of $\sqrt\rho$. For every real $\tau\ge0$ and every initial density matrix $\rho_0$,
--   $$\|e^{\tau\mathcal L}(\rho_0)-\rho\|_1\le e^{-\lambda\tau}\sqrt d\,e^{\beta\|H\|}.$$
--   Consequently, for every real $0<\epsilon<1$,
--   $$t_{\rm mix}(\epsilon)\le\frac1\lambda\left(\frac12\log d+\beta\|H\|+\log\frac1\epsilon\right).$$
--   Both the all-times bound and the continuous-time infimum are retained. This general implication supplies the final mixing conclusion after the gap has been established.
--
--   Differences from the source:
--   - generalization: the SYK setting of Section 2 → any nonzero finite dimension, Hermitian Hamiltonian, and Hermitian coupling family with the computed sampler; reason: the implication uses the Gibbs discriminant gap and Hermiticity, and specializes to every source Majorana family
--   - encoding: real infimum of successful times and trace norm → ENNReal mixing time bounded by ofReal of the source expression; reason: the successful-time set may otherwise be empty; positive rate and error domain make the displayed bound nonnegative
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 12, Eqs. (2.29), (2.32)–(2.33)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem eq_2_33 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (hH : H.IsHermitian)
    (hγ : ∀ i, (γ i).IsHermitian) (β rate : ℝ) (hβ : 0 ≤ β) (hrate : 0 < rate)
    (hgap : HasGap (discriminant H γ β) (gibbsRoot H β) rate) :
  (∀ τ : ℝ, 0 ≤ τ → ∀ X, IsDensity X →
    traceNorm (evolve (lindblad H γ β) τ X - gibbs H β) ≤
      Real.exp (-rate * τ) * Real.sqrt (Fintype.card ι : ℝ) * Real.exp (β * SYKEdge.opNorm H)) ∧
  (∀ ε : ℝ, 0 < ε → ε < 1 →
    mixingTime (lindblad H γ β) (gibbs H β) ε ≤
      ENNReal.ofReal ((1 / rate) * ((1/2 : ℝ) * Real.log (Fintype.card ι : ℝ) +
        β * SYKEdge.opNorm H + Real.log (1/ε)))) := by sorry

end SYKFastMix.FastMixing
