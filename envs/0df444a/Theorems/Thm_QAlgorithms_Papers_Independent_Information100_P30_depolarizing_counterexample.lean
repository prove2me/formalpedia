-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P30_depolarizing_counterexample
-- name    : QAlgorithms.Papers.Independent.Information100.P30.depolarizing_counterexample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:23:50.823913+00:00
-- url     : https://prove2.me/theorems/410b12b4-a175-4305-89be-11eabf1caa33
-- title:
--   EA parallel pair with neither factor EB
-- statement:
--   Define $\mathcal E_q(X)=qX+(1-q)\operatorname{Tr}(X)I/2$ on qubit matrices. The maps at $q=1/2$ and $q=1/4$ are CPTP, and
--
--   $$\mathcal E_{1/2}\otimes\mathcal E_{1/2}\in\mathrm{EA},\quad\mathcal E_{1/2}\notin\mathrm{EB},\quad\mathcal E_{1/2}\circ\mathcal E_{1/2}=\mathcal E_{1/4}\in\mathrm{EB}.$$
--
--   Thus parallel EA does not force either local factor to be EB. The parameter is the retained signal, rather than the noise fraction; only this concrete example is asserted.
-- source:
--   Feasibility Ordering of Entanglement-Source Placement for Qubit Channels, arXiv:2609.18803v1, PDF p. 4, Remark 2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Remark 2 (PDF p.4, Eq.(46)): the concrete parallel EA pair at q = 1/2
has neither factor EB, while its q = 1/4 composition is EB. -/
theorem depolarizing_counterexample :
    IsQubitChannel (depolarizing (1/2)) ∧ IsQubitChannel (depolarizing (1/4)) ∧
    IsParallelEA (depolarizing (1/2)) (depolarizing (1/2)) ∧
    ¬ Entanglement.IsEntanglementBreaking (depolarizing (1/2)) ∧
    (depolarizing (1/2)).comp (depolarizing (1/2)) = depolarizing (1/4) ∧
    Entanglement.IsEntanglementBreaking (depolarizing (1/4)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P30

end
