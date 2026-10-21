-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_corollary1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.corollary1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:52:41.329127+00:00
-- url     : https://prove2.me/theorems/d97f39ca-8b79-4b1d-a774-930749e648a6
-- title:
--   Corollary 1: Schmidt-stratified Choi–Jamiolkowski correspondence
-- statement:
--   Let $H,H',K$ be separable complex Hilbert spaces and let $|\psi\rangle\langle\psi|$ have faithful marginals on $H,K$. Put $\sigma=\operatorname{Tr}_H|\psi\rangle\langle\psi|$ and $C_\sigma=\{\rho:\operatorname{Tr}_{H'}\rho=\sigma\}$. For every $k\ge1$, the map
--
--   $$\Phi\longmapsto(\Phi\otimes\operatorname{Id}_K)(|\psi\rangle\langle\psi|)$$
--
--   restricts to a homeomorphism from $\mathcal P_k(H,H')$, with strong channel topology, onto the closed state subset $S_k\cap C_\sigma$, with trace-norm topology. For $k\ge2$ it sends $\mathcal P_k\setminus\mathcal P_{k-1}$ exactly onto $(S_k\setminus S_{k-1})\cap C_\sigma$.
--
--   This retains both topology and the exact Schmidt strata of the correspondence.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 12, Corollary 1: Schmidt-stratified Choi–Jamiolkowski correspondence

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

/-- arXiv:1110.4363v3, PDF pp.11–12, Corollary 1. The homeomorphism is the
actual faithful-purification Choi map; its image is closed and the strata correspond.
No infinite-dimensional maximally entangled vector is introduced. -/
theorem corollary1 {I J A : Type} [Countable I] [Countable J] [Countable A]
    (k : ℕ) (hk : 0 < k) (psi : PureState (I × A))
    (hleft : faithful (traceSecond psi.val.coefficients))
    (hright : faithful (traceFirst psi.val.coefficients)) :
    let imageSet : Set (State (J × A)) :=
      {rho | rho ∈ schmidtClass J A k ∧ traceFirst rho.coefficients = traceFirst psi.val.coefficients}
    IsClosed imageSet ∧
    ∃ e : {Phi : CanonicalChannel I J // isPEB k Phi} ≃ₜ imageSet,
      (∀ Phi, (e Phi).val.coefficients = tensorApply (canonicalChannelAction Phi.val) psi.val.coefficients) ∧
      (2 ≤ k → ∀ Phi, (¬ isPEB (k - 1) Phi.val ↔
        (e Phi).val ∈ schmidtClass J A k \ schmidtClass J A (k - 1))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
