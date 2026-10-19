-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_l1_distance_faithfulness
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.l1_distance_faithfulness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:24:00.315164+00:00
-- url     : https://prove2.me/theorems/ca12cf48-ddbf-4b05-8083-75a7e147c668
-- title:
--   Entrywise-l1 minimum and faithfulness
-- statement:
--   For any density matrix $\rho$ in dimension $d\ge1$, $\Delta\rho$ is incoherent and minimizes the entrywise absolute-sum distance:
--   $$\min_{\delta\ {\rm diagonal}}\sum_{i,j}|\rho_{ij}-\delta_{ij}|=\sum_{i\ne j}|\rho_{ij}|=\sum_{i,j}|\rho_{ij}-(\Delta\rho)_{ij}|.$$
--   This value is nonnegative and is zero exactly when $\rho$ is diagonal. This is the entrywise norm, counting both ordered positions, with no factor one half.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Eqs.(2), (9), (C1’), PDF p. 3. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


























































/-- PDF pp.1,3, (2), (9): the entrywise-l1 minimum, nonnegativity and faithfulness. -/
theorem l1_distance_faithfulness :
    (∀ d, 0 < d → ∀ rho : CoherenceMatrix d, IsDensityMatrix rho →
      IncoherentState (dephasedMatrix rho) ∧
      entrywiseDistance rho (dephasedMatrix rho) = Coherence.l1Coherence rho ∧
      distanceCandidate entrywiseDistance rho = Coherence.l1Coherence rho ∧
      ∀ delta, IncoherentState delta → Coherence.l1Coherence rho ≤ entrywiseDistance rho delta) ∧
    CoherenceNonnegative (fun _ rho => Coherence.l1Coherence rho) ∧
    CoherenceFaithful (fun _ rho => Coherence.l1Coherence rho) := by sorry








end QAlgorithms.Papers.Independent.Independent1.P04
