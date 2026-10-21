-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_example15
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.example15
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:57:06.565313+00:00
-- url     : https://prove2.me/theorems/7a1e2626-7fd4-4eeb-9a8f-4e0634c8a421
-- title:
--   Unnumbered Appendix 6.2 example, equation (15)
-- statement:
--   Let $k\ge1$ and let $(u_i)_{i=1}^k,(v_i)_{i=1}^k$ be orthonormal families in normalized circle $L^2$, every member having all Fourier coefficients nonzero. Let $(e_i)$ be the orthonormal basis of $\mathbb C^k$ and put $\Omega=k^{-1/2}\sum_i u_i\otimes v_i\otimes e_i$. For positive integers $n$ define
--
--   $$\rho_n=\frac{n}{2\pi}\int_0^{2\pi/n}(V_x\otimes V_x\otimes I)|\Omega\rangle\langle\Omega|(V_x\otimes V_x\otimes I)^*\,dx.$$
--
--   Use the bipartition $H_1\otimes(H_2\otimes\mathbb C^k)$. The vector $\Omega$ is normalized and has Schmidt rank $k$. Every $\rho_n$ is a density state with $\mathrm{SN}(\rho_n)\le k$ and no positive finite-Schmidt-rank pure suboperator; hence all positive-weight components of any countable pure decomposition have infinite Schmidt rank. Moreover $\rho_n\to|\Omega\rangle\langle\Omega|$ in trace norm and $\mathrm{SN}(\rho_n)=k$ eventually.
--
--   This supplies the explicit construction of states of each finite Schmidt number with the stated decomposition pathology.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 18, Unnumbered Appendix 6.2 example, equation (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- arXiv:1110.4363v3, PDF pp.18–19, Appendix 6.2 example, (15).
The constructed states, their limit, upper bound and eventual exact Schmidt number
are retained, as is the absence of finite-Schmidt-rank pure suboperators for every
positive n. On p.19 the proof's k*lambda*nu should be k*lambda*nu^2; only positivity
is used. Short averages are dominated by n times the full-period average. -/
theorem example15 (k : ℕ) (hk : 0 < k) (u v : Fin k → Hilbert ℤ)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v)
    (huc : ∀ i j, u i j ≠ 0) (hvc : ∀ i j, v i j ≠ 0) :
    ∃ (omega : PureState (ℤ × (ℤ × Fin k)))
      (r : ℕ → State (ℤ × (ℤ × Fin k))),
      (∃ z : Hilbert (ℤ × (ℤ × Fin k)), (∀ p, z p = omegaCoeff u v p) ∧
        ‖z‖ = 1 ∧ omega.val.coefficients = rankOne z) ∧
      schmidtRank omega = (k : ℝ≥0∞) ∧
      (∀ n, (r n).coefficients = shortTwirl u v (n + 1) ∧
        r n ∈ schmidtClass ℤ (ℤ × Fin k) k ∧ noFinitePurePart (r n) ∧
        allEnsembleRanksInfinite (r n)) ∧
      Tendsto r atTop (nhds omega.val) ∧
      (∃ N, ∀ n ≥ N, continuousSchmidtNumber (r n) = (k : ℝ≥0∞)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
