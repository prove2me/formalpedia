-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_selective_convex_implies_monotone
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.selective_convex_implies_monotone
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:23:22.765878+00:00
-- url     : https://prove2.me/theorems/8dc42177-d2e5-48f2-9a82-ab285df6cc17
-- title:
--   Selective monotonicity and convexity imply monotonicity
-- statement:
--   Let $C_d$ be a nonnegative real functional on density matrices for every finite dimension $d\ge1$. Suppose it is convex on finite ensembles and satisfies selective monotonicity for every complete incoherent Kraus family, allowing different positive output dimensions per branch. Zero-probability branches contribute zero. Then for every incoherent family with a common output dimension,
--   $$C_{d_{\rm out}}\left(\sum_a K_a\rho K_a^\dagger\right)\le C_{d_{\rm in}}(\rho).$$
--   This implication requires no faithfulness hypothesis.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Coherence measures, (C2a)–(C3), PDF p. 3. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

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


















































/-- PDF pp.2–3: (C2b) and (C3) imply (C2a); no (C1) premise is required. -/
theorem selective_convex_implies_monotone (C : (d : ℕ) → CoherenceMatrix d → ℝ)
    (hC : CoherenceNonnegative C)
    (hselective : CoherenceSelective C) (hconvex : CoherenceConvex C) :
    CoherenceMonotone C := by sorry
















end QAlgorithms.Papers.Independent.Independent1.P04
