-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorSplit_separator_add_childPotential_le
-- name    : QEC.Locality.BGKLSeparatorSplit.separator_add_childPotential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:35:14.303107+00:00
-- url     : https://prove2.me/theorems/c3026d74-f69b-475a-8c95-330f20515b56
-- title:
--   BGKLSeparator Split: separator add child Potential le
-- statement:
--   One separator plus one child's remaining potential fits the parent's potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L365-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L365-L400

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.BGKLSeparatorSplit.separator_add_childPotential_le
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices child : Finset ι} (split : BGKLSeparatorSplit P vertices)
    {beta exponent : ℝ}
    (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    (hSeparator : (split.separator.card : ℝ) ≤
      beta * Real.rpow vertices.card exponent)
    (hChild : Real.rpow child.card exponent ≤
      bgklDecayRatio exponent * Real.rpow vertices.card exponent) :
    (split.separator.card : ℝ) +
        beta / (1 - bgklDecayRatio exponent) * Real.rpow child.card exponent ≤
      beta / (1 - bgklDecayRatio exponent) * Real.rpow vertices.card exponent := by sorry
