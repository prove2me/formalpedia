-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_conversion_via_ebits
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.conversion_via_ebits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:11:41.785062+00:00
-- url     : https://prove2.me/theorems/679c35fd-a714-4606-8271-dc77503a40d1
-- title:
--   Eq.(20): conversion by distillation followed by preparation
-- statement:
--   Let $\rho$ and $\sigma$ be densities on positive finite bipartite systems, which may have different local dimensions. Define $E_d$ and $E_c$ operationally as the optimal LOCC Bell-pair yield and preparation supply. If $E_c(\sigma)>0$, then
--
--   $$\rho\longrightarrow\sigma^{\otimes E_d(\rho)/E_c(\sigma)}$$
--
--   is an actual asymptotic LOCC conversion, with arbitrary positive error and rate slack and all sufficiently large integer block lengths. At zero yield this is disposal. The strict cost guard excludes division by zero; the statement requires neither a measure $E$ nor finite-block attainment.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 3, Eq.(20): conversion by distillation followed by preparation

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF p.3 (20): distillation followed by preparation at the limiting
rate, with the arbitrary positive slack already in Converts. Cost zero is
excluded; zero yield is disposal. No finite-block optimizer is assumed. -/
theorem conversion_via_ebits
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (rho : VidalOperator a b) (sigma : VidalOperator c d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hcost : 0 < loccEntanglementCost sigma) :
    AsymptoticLOCCConverts (single rho 1) (single sigma (loccDistillable rho / loccEntanglementCost sigma)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
