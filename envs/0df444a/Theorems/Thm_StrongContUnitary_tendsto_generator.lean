-- Prove2me | Theorems.Thm_StrongContUnitary_tendsto_generator
-- name    : StrongContUnitary.tendsto_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:57.917494+00:00
-- url     : https://prove2.me/theorems/438cd018-8442-5d69-a5ec-d8e4a366057c
-- title:
--   Strong Cont Unitary: tendsto generator
-- statement:
--   On its domain, the Stone difference quotient converges to the generator.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Generator.lean#L120-L124
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Generator.lean#L120-L124

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Algebra.Star.Unitary
import Definitions.Def_Spectral_Stone_Generator
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open StrongContUnitary

theorem StrongContUnitary.tendsto_generator (U : StrongContUnitary E) (x : U.generator.domain) :
    Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t (x : E) - x))
      (nhdsWithin 0 {0}ᶜ) (nhds (U.generator x)) := by sorry
