-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_localIsometryInvariance
-- name    : QAlgorithms.Papers.Independent.Information100.P21.localIsometryInvariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:58:26.708484+00:00
-- url     : https://prove2.me/theorems/f5fe7a0d-a461-42b3-802a-4073819790e0
-- title:
--   IX.20 — Proposition IX.20 (Local isometry invariance). Let VA : CdA → CDA and VB : CdB → CDB be isometries, and put
-- statement:
--   Let $V_A,V_B$ be rectangular local isometries between positive finite complex registers, and let $\rho$ be a density operator. Put $V=V_A\otimes V_B$. With the actual bipartite separable cone,
--   $$R_s(V\rho V^\dagger)=R_s(\rho),\qquad R_g(V\rho V^\dagger)=R_g(\rho).$$
--   This preserves the cost in larger ambient registers without replacing separability by PPT.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 27, IX.20 — Proposition IX.20 (Local isometry invariance). Let VA : CdA → CDA and VB : CdB → CDB be isometries, and put

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 27, Proposition IX.20 (Local isometry invariance). Let VA : CdA → CDA and VB : CdB → CDB be isometries, and put. -/
theorem localIsometryInvariance {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
  [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
  (VA : Matrix K I ℂ) (VB : Matrix L J ℂ) (hA : VAᴴ*VA=1) (hB : VBᴴ*VB=1)
  (rho : Op (I × J)) (h : QAlgorithms.IsDensityMatrix rho) :
  let V := Matrix.kronecker VA VB
  rs (V*rho*Vᴴ)=rs rho ∧ rg (V*rho*Vᴴ)=rg rho := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
