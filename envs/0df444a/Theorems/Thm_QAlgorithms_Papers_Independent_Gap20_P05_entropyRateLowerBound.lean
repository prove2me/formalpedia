-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_entropyRateLowerBound
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.entropyRateLowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:11:20.352737+00:00
-- url     : https://prove2.me/theorems/cff18d2b-3b5d-45a7-ab60-9e63d31961d3
-- title:
--   Lemma 5: entropy lower bound per copy
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   Let $\omega$ be any finite-rank state on $H_A$, and let $\omega_n$ be arbitrary states on the completed $n$-copy space, $n\ge1$, with $\|\omega_n-\omega^{\otimes n}\|_1\to0$. Then
--
--   $$S(\omega)<+\infty,\qquad S(\omega)\le\liminf_{n\to\infty}\frac{S(\omega_n)}{n}.$$
--
--   The liminf is in the extended nonnegative reals. The approximants need no energy bound, purity or entropy finiteness. This is the entropy-rate lower bound used in the asymptotic results.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 6, Lemma 5: entropy lower bound per copy

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P05

noncomputable section

open Filter

open scoped ENNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap20.P05

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity rankOne traceSize traceClosure IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (generalizedRelativeEntropy traceSecond)

open QAlgorithms.Entanglement (partialTransposeFirst)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartitePower)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

/-- Lemma 5, PDF pp.6--7, (17): finite operator rank of the one-system state,
without purity or energy bounds on the approximants. Liminf is extended-valued. -/
theorem entropyRateLowerBound (omega : State ℕ) (hfinite : FiniteRank omega.coefficients)
    (rho : (k : ℕ) → State (Fin (k + 1) → ℕ))
    (hlim : Tendsto (fun k => traceSize ((rho k).coefficients -
      tensorPower (k + 1) omega.coefficients)) atTop (𝓝 (0 : ℝ≥0∞))) :
    entropyBits omega.coefficients < ⊤ ∧
    entropyBits omega.coefficients ≤
      liminf (fun k => entropyBits (rho k).coefficients / (k + 1 : ℝ≥0∞)) atTop := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
