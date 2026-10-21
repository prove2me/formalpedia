-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_accessible_eq_holevo_iff_commuting
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.accessible_eq_holevo_iff_commuting
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:05:29.991275+00:00
-- url     : https://prove2.me/theorems/746c7795-4236-4be3-ac44-8b4d8d41dbbe
-- title:
--   Example 9, unnumbered: accessible information attains Holevo iff supported states commute
-- statement:
--   Let $\{p_x,\rho_x\}$ be a normalized finite density ensemble on a nonzero finite-dimensional space. For a finite POVM $M=\{M_y\}$ put $P_M(x,y)=p_x\operatorname{Tr}(M_y\rho_x)$, and define $I_{\mathrm{acc}}=\sup_M I(X:Y)_{P_M}$, ranging over every positive finite number of outcomes and every such POVM. Then
--
--   $$I_{\mathrm{acc}}=\chi(\{p_x,\rho_x\})\quad\Longleftrightarrow\quad[\rho_x,\rho_{x'}]=0\ \text{whenever }p_x>0,\ p_{x'}>0.$$
--
--   All information is in bits. The score set is nonempty and bounded for this ensemble, so its real supremum has its usual meaning. This is Holevo's saturation criterion [5], with the source's null-label reduction made explicit.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 6, Example 9, unnumbered: accessible information attains Holevo iff supported states commute

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

/-- PDF p.6, Example 9, credit Holevo [5]: saturation concerns supported ensemble members. -/
theorem accessible_eq_holevo_iff_commuting {X H : Type}
    [Fintype X] [Fintype H] [Nonempty X] [Nonempty H] (e : CQData X H) (he : e.Valid) :
    accessibleInformation e = ensembleInformation e ↔ ∀ x y, 0 < e.prob x → 0 < e.prob y →
      e.state x * e.state y = e.state y * e.state x := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
