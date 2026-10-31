-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_two_by_N_distillation_boundary
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.two_by_N_distillation_boundary
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:14:52.532233+00:00
-- url     : https://prove2.me/theorems/bd42eadc-2f57-4159-9cd1-2a3ea9c03fd3
-- title:
--   Unnumbered main result: distillable entanglement at the 2 by N boundary
-- statement:
--   Fix a positive finite local dimension $b$ in a $2\times b$ bipartite system. Let $E_d$ be the operational ordinary-LOCC Bell-pair rate and let $\mathcal D=\{\rho:E_d(\rho)>0\}$. At each density-relative frontier point $\rho$ of $\mathcal D$,
--
--   $$E_d(\rho)=0,\qquad E_d\text{ is continuous at }\rho.$$
--
--   This is a statement about distillable entanglement itself. The dimension $b$ is not a copy count; for $b=1$ the frontier is empty.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 3, Unnumbered main result: distillable entanglement at the 2 by N boundary

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF pp.1,3–4: ordinary distillable entanglement continuously vanishes
at the 2 by N boundary. N is a positive local dimension, not a copy count. -/
theorem two_by_N_distillation_boundary
    (b : ℕ) (hb : 0 < b) (rho : DensitySpace 2 b)
    (hboundary : rho ∈ frontier {sigma : DensitySpace 2 b | 0 < loccDistillable sigma.val}) :
    loccDistillable rho.val = 0 ∧
      ContinuousAt (fun sigma : DensitySpace 2 b => loccDistillable sigma.val) rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
