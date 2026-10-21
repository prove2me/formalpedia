-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_cq_identity_and_holevo
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.cq_identity_and_holevo
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:59:28.856075+00:00
-- url     : https://prove2.me/theorems/d01f3dd1-ba76-4f60-b90f-a030e7d5668d
-- title:
--   Example 2: Holevo information as cq mutual information and measurement bound
-- statement:
--   Let $\{p_x,\rho_x\}_{x\in X}$ be a finite ensemble on a nonzero finite-dimensional space $H$, with $p_x\ge0$, $\sum_xp_x=1$, and each $\rho_x$ a density operator. Put $\bar\rho=\sum_xp_x\rho_x$, $\chi=S(\bar\rho)-\sum_xp_xS(\rho_x)$, and $\rho_{XH}=\sum_xp_x|x\rangle\langle x|\otimes\rho_x$. Then
--
--   $$\chi=I(X:H)_{\rho_{XH}},\qquad I(X:Y)\le\chi.$$
--
--   Here the second inequality holds for every finite POVM $\{M_y\}$, with the actual joint law $P(x,y)=p_x\operatorname{Tr}(M_y\rho_x)$. Quantum mutual information is $S(\rho_X)+S(\rho_H)-S(\rho_{XH})$, and classical mutual information is computed from $P$. All information is in bits. The identity relates ensembles to bipartite states; the measurement bound is credited by the source to Holevo [5].
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 3, Example 2: Holevo information as cq mutual information and measurement bound

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35

noncomputable section

open scoped Matrix ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Renew46.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted interfaces, inspected in the pinned library.

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P21 (petz)

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumMI)

/-- PDF p.3, Example 2: cq mutual-information identity and Holevo's measurement bound [5]. -/
theorem cq_identity_and_holevo {X H : Type} [Fintype X] [Fintype H]
    [Nonempty X] [Nonempty H] (e : CQData X H) (he : e.Valid) :
    ensembleInformation e = quantumMI (cqState e.prob e.state) ∧
    ∀ n : ℕ, ∀ m : Fin n → Matrix H H ℂ, IsPOVM m →
      mutualInfoBits (measurementLaw e m) ≤ ensembleInformation e := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
