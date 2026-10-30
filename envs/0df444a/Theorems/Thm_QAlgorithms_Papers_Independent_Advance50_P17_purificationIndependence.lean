-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_purificationIndependence
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.purificationIndependence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:36:37.213114+00:00
-- url     : https://prove2.me/theorems/70c17909-5c89-4af9-ba5c-d4f124919713
-- title:
--   Appendix A2: channel-pair fidelity is independent of purification
-- statement:
--   Fix CPTP maps $\mathcal E,\mathcal F$ and an input density matrix $\rho$ on a $d$-dimensional system. Define $|\psi_\rho\rangle=\sum_{a,i}(\sqrt\rho)_{ia}|a\rangle|i\rangle$ and let $G_F(\rho)$ and $G_D(\rho)$ be respectively squared fidelity and half trace-norm distance of its two extended channel outputs. For any unit purification $\psi$ of $\rho$ on $A\otimes I$ with $\dim A\ge d$,
--
--   $$F((\mathcal I_A\otimes\mathcal E)(\psi),(\mathcal I_A\otimes\mathcal F)(\psi))=G_F(\rho),\qquad D((\mathcal I_A\otimes\mathcal E)(\psi),(\mathcal I_A\otimes\mathcal F)(\psi))=G_D(\rho).$$
--
--   The canonical objectives therefore do not depend on the choice or size of purification.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 12, Appendix A2: channel-pair fidelity is independent of purification

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Appendix A2, PDF p.12: both canonical objectives are independent of the purification.
The purification and marginal are actual normalized data, not an assumed objective value. -/
theorem purificationIndependence (E F : FiniteProcess I I) (rho : ProcessDensityInput I)
    (hdim : Fintype.card I ≤ Fintype.card J) (psi : ProcessPureInput (J × I))
    (hp : traceLeft (pureDensity psi.val) = rho.val) :
    fidelity (idTensorSuperop E.val (pureDensity psi.val))
      (idTensorSuperop F.val (pureDensity psi.val)) = purifiedFidelity E.val F.val rho.val ∧
    traceDistance (idTensorSuperop E.val (pureDensity psi.val))
      (idTensorSuperop F.val (pureDensity psi.val)) = purifiedChannelTraceDistance E.val F.val rho.val := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
