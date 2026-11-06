-- Prove2me | Theorems.Thm_ProbabilityTheory_isPositiveDefinite_exp_ofReal_mul
-- name    : ProbabilityTheory.isPositiveDefinite_exp_ofReal_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:58:03.376001+00:00
-- url     : https://prove2.me/theorems/5494dcdb-1953-4237-bc38-3e15fecbbf4c
-- title:
--   LeanLevy: ProbabilityTheory.isPositiveDefinite_exp_ofReal_mul
-- statement:
--   The exponential `ξ ↦ exp(x·ξ·I)` is positive definite: it is the characteristic Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/PositiveDefinite.lean#L328

import Definitions.Def_LeanLevy_Fourier_PositiveDefinite
import Definitions.Def_LeanLevy_Probability_Characteristic
import Mathlib.Analysis.Matrix.PosDef

theorem ProbabilityTheory.isPositiveDefinite_exp_ofReal_mul : ∀ (x : Real),
  ProbabilityTheory.IsPositiveDefinite fun ξ =>
    Complex.exp
      (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
        (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) ↑x ↑ξ) Complex.I) := by sorry
