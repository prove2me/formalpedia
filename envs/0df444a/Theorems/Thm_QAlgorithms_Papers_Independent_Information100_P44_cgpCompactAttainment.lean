-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_cgpCompactAttainment
-- name    : QAlgorithms.Papers.Independent.Information100.P44.cgpCompactAttainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:38:48.564742+00:00
-- url     : https://prove2.me/theorems/2fc1c530-c64d-433a-99ec-0c522433df96
-- title:
--   Lemma 3: compactness and optimum attainment of CGP feasible set
-- statement:
--   For the fixed four-level instance $H=\operatorname{diag}(0,1,1,3)$, $\beta=1$, input $\rho$ of Eq. (111), and coarse target populations $(1/2,7/20,3/20)$, let $\mathcal J$ be the set of output-first unnormalized Choi matrices satisfying the full CGP constraints and these population constraints. Then
--   $$\mathcal J\text{ is compact},\qquad \mathcal J\ne\varnothing\ \Longrightarrow\ \text{each of the three directional objectives and their sum attains a maximum on }\mathcal J.$$
--   Compactness does not assume nonemptiness. This supplies the attainment statement for the finite-dimensional SDP representation of the source's feasible channel set.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 17, Lemma 3: compactness and optimum attainment of CGP feasible set

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.17, Lemma 3: compactness does not assume nonemptiness; attainment is conditional. -/
theorem cgpCompactAttainment :
    IsCompact {J | FixedChoiFeasible J} ∧
    (({J | FixedChoiFeasible J} : Set (Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)).Nonempty →
      (∀ k : Fin 3, ∃ J, FixedChoiFeasible J ∧
        ∀ K, FixedChoiFeasible K → channelObjective k (fromChoi K) ≤ channelObjective k (fromChoi J)) ∧
      ∃ J, FixedChoiFeasible J ∧ ∀ K, FixedChoiFeasible K →
        (∑ k : Fin 3, channelObjective k (fromChoi K)) ≤ ∑ k : Fin 3, channelObjective k (fromChoi J)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
