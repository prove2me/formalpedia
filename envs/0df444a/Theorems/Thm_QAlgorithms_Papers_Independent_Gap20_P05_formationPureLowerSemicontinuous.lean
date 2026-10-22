-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_formationPureLowerSemicontinuous
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.formationPureLowerSemicontinuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:13:04.172236+00:00
-- url     : https://prove2.me/theorems/a413f9eb-5b49-4e0d-928b-5b4646cf24ec
-- title:
--   Pure-point lower semicontinuity of countable formation
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   Here $E_F(\rho)$ is the infimum of $\sum_i p_i E(|u_i\rangle\langle u_i|)$ over countable normalized pure-state decompositions $\rho=\sum_i p_i|u_i\rangle\langle u_i|$ converging in trace norm. Components need not satisfy any energy constraint, and the infimum need not be attained.
--
--   Let $\sigma$ be any pure state, and let $\rho_k$ be arbitrary states with $\|\rho_k-\sigma\|_1\to0$. Then
--
--   $$E_F(\sigma)\le\liminf_{k\to\infty}E_F(\rho_k).$$
--
--   No energy bound is imposed and infinite values are retained. This asserts lower semicontinuity at pure points only.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 10, §III, unnumbered: pure-point lower semicontinuity without an energy bound

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

/-- Unnumbered conclusion of the first half of Proposition 6, PDF pp.9--10:
lower semicontinuity at pure states, with no energy bound and allowing infinity. -/
theorem formationPureLowerSemicontinuous (sigma : PureState (ℕ × ℕ))
    (rho : ℕ → State (ℕ × ℕ))
    (hlim : Tendsto (fun k => traceSize ((rho k).coefficients - sigma.val.coefficients))
      atTop (𝓝 (0 : ℝ≥0∞))) :
    countableFormationBits sigma.val.coefficients ≤ liminf (fun k => countableFormationBits (rho k).coefficients) atTop := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
