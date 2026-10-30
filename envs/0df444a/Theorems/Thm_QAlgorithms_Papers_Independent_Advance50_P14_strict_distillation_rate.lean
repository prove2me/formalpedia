-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_strict_distillation_rate
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.strict_distillation_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:17:16.560982+00:00
-- url     : https://prove2.me/theorems/8e8d4e88-4fff-4ef2-9241-c06189e24eb5
-- title:
--   Proposition IV.4, equations (14)–(15): strict-map distillation
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. For an entangled state $\rho$, let $E_D^{\rm ne}$ be the supremum of liminf Bell-pair yields over protocols with vanishing full trace-norm output error, whose CPTP maps preserve separability exactly at every blocklength. Then
--
--   $$E_D^{\rm ne}(\rho)=E_R^\infty(\rho).$$
--
--   No finite-block entanglement generation is allowed. The entangled-state hypothesis is the one printed in the proposition.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 12, Proposition IV.4, equations (14)–(15): strict-map distillation

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.12, Proposition IV.4, Eq.(15): distillation by exactly non-entangling
maps at every blocklength. The printed entangled-state hypothesis is retained. -/
theorem strict_distillation_rate {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (hrho : IsDensityMatrix rho) (hentangled : ¬ IsMultipartiteSeparable A rho) :
    distillableEntanglement .strict A rho =
      ENNReal.ofReal (regularizedMultipartiteEntanglement A rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
