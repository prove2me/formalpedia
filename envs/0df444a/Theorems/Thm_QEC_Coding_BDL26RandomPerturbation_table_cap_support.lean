-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_table_cap_support
-- name    : QEC.Coding.BDL26RandomPerturbation.table_cap_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:49:51.011592+00:00
-- url     : https://prove2.me/theorems/f769a2a0-cd40-4928-bb91-0efb082bb13e
-- title:
--   BDL26 Random Perturbation: table cap support
-- statement:
--   Every entry, including all future resampling columns, has the required support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L40-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean#L40-L54

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_TriangleHit
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Sampling
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26RandomPerturbation.table_cap_support (P : TannerSquarePresentation) {R c : ℝ} (hR : 0 < R)
    (hc : c < 1) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    ∀ᵐ T ∂tableLaw (vertexLaw P R c), ∀ p : Vertex P × ℕ,
      T p ∈ displacementCap R (vertexAxis P p.1) c := by sorry
