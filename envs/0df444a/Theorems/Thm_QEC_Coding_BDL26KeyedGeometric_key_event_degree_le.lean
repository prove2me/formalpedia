-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_event_degree_le
-- name    : QEC.Coding.BDL26KeyedGeometric.key_event_degree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:01:34.205497+00:00
-- url     : https://prove2.me/theorems/811892b6-3877-45f5-9767-9424da5fff23
-- title:
--   BDL26 Keyed Geometric: key event degree le
-- statement:
--   The derived degree bound contains no perturbation scale or global input size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricCounts.lean#L97-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricCounts.lean#L97-L112

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26KeyedGeometric.key_event_degree_le (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (K M : ℕ)
    (hv : BoundedValence P) (hpool : ∀ a, (localPool P J K a).card ≤ M)
    (e : KeyEvent P key hk J K) :
    ((supportGraph (keySupport P key hk J K)).neighborFinset e).card ≤ 12*56*M^3 := by sorry
