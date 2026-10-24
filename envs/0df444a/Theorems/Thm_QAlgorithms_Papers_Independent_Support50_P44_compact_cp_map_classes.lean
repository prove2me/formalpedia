-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_compact_cp_map_classes
-- name    : QAlgorithms.Papers.Independent.Support50.P44.compact_cp_map_classes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-24T00:04:34.003353+00:00
-- url     : https://prove2.me/theorems/3b8ea7ff-0226-4621-9553-0cb11a8e97e9
-- title:
--   Compact finite completely positive map classes
-- statement:
--   Let $E,G$ be finite-dimensional complex Hilbert spaces. In the topology of the entries of a linear map, equivalently its Choi matrix, both classes
--
--   $$\{\Phi:E\to G:\Phi\text{ completely positive and trace nonincreasing}\},\qquad\{\Phi:E\to G:\Phi\text{ completely positive and trace preserving}\}$$
--
--   are compact. Trace nonincrease is imposed on every positive input. This includes quantum operations that are not channels and supplies compactness for compressed recovery maps.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 26, Remark C.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A B C E G : Type*}

/-- PDF p.26, Remark C.3: both TNI CP and TP CP map classes, in the finite
linear-map coordinate topology. No nonemptiness is needed for compactness. -/
theorem compact_cp_map_classes [Fintype E] [Fintype G]
    [DecidableEq E] [DecidableEq G] :
    letI := finiteMapTopology (E := E) (G := G)
    IsCompact {Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ | FiniteCP Phi ∧ FiniteTNI Phi} ∧
    IsCompact {Phi : Matrix E E ℂ →ₗ[ℂ] Matrix G G ℂ | FiniteCP Phi ∧ FiniteTP Phi} := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
