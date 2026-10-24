-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P16_entanglementAssisted_capacityBound
-- name    : QAlgorithms.Papers.Independent.Gap20.P16.entanglementAssisted_capacityBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:39:24.517382+00:00
-- url     : https://prove2.me/theorems/e2c6c476-933e-419f-a092-c57d99866080
-- title:
--   General entanglement-assisted capacity upper bound
-- statement:
--   Let $d\ge1$ and let $\Phi$ be any completely positive trace-preserving map on the complex $d\times d$ matrices. Let $H$ denote von Neumann entropy in bits and $H(\rho,\Phi)$ the entropy exchange obtained by applying the channel to one half of a purification of the density matrix $\rho$. Define $C_{\rm ea}(\Phi)=\max_\rho[H(\rho)+H(\Phi(\rho))-H(\rho,\Phi)]$, and let $\bar C^{(1)}(\Phi)$ be the maximum output Holevo quantity over all finite normalized input state ensembles. Then
--
--   $$
--   C_{\rm ea}(\Phi)\le\log_2 d+\bar C^{(1)}(\Phi).
--   $$
--
--   The right-hand capacity is single-use. This bounds the possible entanglement-assisted improvement for every channel in the paper's finite-dimensional setting.
-- source:
--   Remarks on the classical capacity of quantum channel, arXiv:quant-ph/0212025v1, PDF p. 4, §2, bound before (12)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P16

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

/-- PDF p.4, section 2, unnumbered bound preceding (12); proof on pp.4--5.
C_ea is the single-input maximum (12), represented by the accepted bounded
supremum maximalMutualInfo; the right side uses the SINGLE-USE Holevo
capacity (1), not its regularization. Both optimizations are over density inputs. -/
theorem entanglementAssisted_capacityBound
    {d : ℕ} (hd : 0 < d) (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi) :
    QAlgorithms.Papers.Independent.Dependency50.P45.maximalMutualInfo Phi ≤
      Real.logb 2 d + QAlgorithms.Papers.Independent.Dependency50.P45.holevoCapacity Phi := by sorry

end QAlgorithms.Papers.Independent.Gap20.P16

end
