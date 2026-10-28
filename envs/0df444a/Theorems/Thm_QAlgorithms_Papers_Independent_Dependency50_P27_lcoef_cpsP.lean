-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_lcoef_cpsP
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.lcoef_cpsP
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:58:47.020978+00:00
-- url     : https://prove2.me/theorems/1c6de208-ae8e-49e9-95d2-721acc5326a1
-- title:
--   §6.2.3, Lemma lcoef_cpsP
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Let $k$ map terms to formulas and let $\bar k:R\to\mathrm{Bool}$. Suppose for every term $t$ and environment list $e$, $\operatorname{qfEval}(e,k(t))=\bar k(\operatorname{eval}(e,t))$. For every formal coefficient list $p$ and environment $e$,
--
--   $$\operatorname{qfEval}(e,\operatorname{lcoefCps}(p,k))=\bar k(\operatorname{lc}(\operatorname{evalPoly}(e,p))).$$
--
--   The complete recursive CPS transform tests vanishing of all interpreted tail coefficients. The universal compatibility assumption is retained, including its quantifier order.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 33, §6.2.3, Lemma lcoef_cpsP

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 33, lcoef_cpsP, retaining universal continuation compatibility. -/
theorem lcoef_cpsP {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (k : Term R → Formula R) (kbar : R → Bool)
    (hk : ∀ (x : Term R) (e : List R), qfEval e (k x) = kbar (evalTerm e x)) :
    ∀ (p : PolyF R) (e : List R),
      qfEval e (lcoefCps p k) = kbar (evalPoly e p).leadingCoeff := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
