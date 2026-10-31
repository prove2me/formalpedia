-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_ppt_assisted_boundary_vanishing
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.ppt_assisted_boundary_vanishing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:15:47.009452+00:00
-- url     : https://prove2.me/theorems/99048aa0-39ad-4700-b3a6-c855c37963b5
-- title:
--   Unnumbered main result: PPT-assisted distillation vanishes at the PPT boundary
-- statement:
--   Fix positive finite bipartite local dimensions. Define $E_d^{\mathrm{LOCC+PPT}}$ as the supremal Bell-pair yield of actual adaptive LOCC protocols supplied with arbitrary positive-partial-transpose densities, whose finite dimensions and states may depend on block length, error and rate slack. At every density-relative frontier point $\rho$ of the NPPT set,
--
--   $$E_d^{\mathrm{LOCC+PPT}}(\rho)=0,\qquad E_d^{\mathrm{LOCC+PPT}}\text{ is continuous at }\rho.$$
--
--   Here NPPT means that the partial transpose is not positive semidefinite. Assistance is physically inserted into an LOCC protocol; the operation class is not replaced by all PPT-preserving channels.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 4, Unnumbered main result: PPT-assisted distillation vanishes at the PPT boundary

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF pp.1,4: LOCC plus actually supplied PPT states, rather than all
PPT-preserving maps, continuously vanishes at the PPT/NPPT frontier. -/
theorem ppt_assisted_boundary_vanishing
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (rho : DensitySpace a b)
    (hboundary : rho ∈ frontier {sigma : DensitySpace a b |
      ¬ (Entanglement.partialTransposeFirst sigma.val).PosSemidef}) :
    pptAssistedDistillable rho.val = 0 ∧
      ContinuousAt (fun sigma : DensitySpace a b => pptAssistedDistillable sigma.val) rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
