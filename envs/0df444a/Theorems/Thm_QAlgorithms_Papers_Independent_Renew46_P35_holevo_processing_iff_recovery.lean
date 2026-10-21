-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_holevo_processing_iff_recovery
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.holevo_processing_iff_recovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:00:33.605348+00:00
-- url     : https://prove2.me/theorems/7b60d97e-c476-4396-8022-bf0341483a8d
-- title:
--   Example 4: Holevo data processing and recovery of each supported ensemble state
-- statement:
--   Let $\{p_x,\rho_x\}$ be a normalized finite density ensemble on $H$, and let $\phi:\mathcal B(H)\to\mathcal B(K)$ be a completely positive trace-preserving map between nonzero finite-dimensional spaces. Let $\bar\rho=\sum_xp_x\rho_x$ and let $\chi$ denote Holevo information in bits. Then
--
--   $$\chi(\{p_x,\phi(\rho_x)\})\le\chi(\{p_x,\rho_x\}).$$
--
--   Equality holds if and only if there is a CPTP map $R:\mathcal B(K)\to\mathcal B(H)$ such that $R\phi(\rho_x)=\rho_x$ for every $x$ with $p_x>0$, and, on the support of $\phi(\bar\rho)$,
--
--   $$R(Z)=\bar\rho^{1/2}\phi^*\!\left(\phi(\bar\rho)^{-1/2}Z\phi(\bar\rho)^{-1/2}\right)\bar\rho^{1/2}.$$
--
--   The inverse is the support inverse; $R$ is a CPTP completion on all operators. The adjoint satisfies $\operatorname{Tr}(\phi^*(Z)X)=\operatorname{Tr}(Z\phi(X))$. This states both data processing and its supported-state equality criterion without assuming individual components are invertible.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 4, Example 4: Holevo data processing and recovery of each supported ensemble state

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

/-- PDF p.4, Example 4, eq.(9): data processing and supported-state recovery by a CPTP
completion of the mean-state transpose map. No invertibility of individual states is assumed. -/
theorem holevo_processing_iff_recovery {X H K : Type}
    [Fintype X] [Fintype H] [Fintype K] [Nonempty X] [Nonempty H] [Nonempty K]
    (e : CQData X H) (he : e.Valid) (f : Superop H K) (hf : IsChannel f) :
    chiAfter e f ≤ ensembleInformation e ∧
    (chiAfter e f = ensembleInformation e ↔ ∃ r : Superop K H, IsChannel r ∧
      (∀ x : Matrix K K ℂ,
        supportProjection (f (ensembleMean e)) * x * supportProjection (f (ensembleMean e)) = x →
          r x = petz (ensembleMean e) f x) ∧
      ∀ x, 0 < e.prob x → r (f (e.state x)) = e.state x) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
