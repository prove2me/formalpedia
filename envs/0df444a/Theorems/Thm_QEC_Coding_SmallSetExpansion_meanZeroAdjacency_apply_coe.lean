-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_meanZeroAdjacency_apply_coe
-- name    : QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:42.160706+00:00
-- url     : https://prove2.me/theorems/6f6c0827-4248-4957-84bf-aa6a4d1b599c
-- title:
--   Small Set Expansion: mean Zero Adjacency apply coe
-- statement:
--   The Small Set Expansion construction uses the mean Zero Adjacency apply coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L276-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L276-L283

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (f : meanZeroEuclideanSubspace (V := V)) (v : V) :
    (meanZeroAdjacency M degree hSymmetric hRegular f :
      EuclideanSpace ℂ V) v =
      complexWeightedNeighborSum M (fun u => f.1 u) v := by sorry

attribute [defeq] QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe
