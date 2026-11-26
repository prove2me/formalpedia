-- Prove2me | Theorems.Thm_StrongContUnitary_mem_generator_domain_iff
-- name    : StrongContUnitary.mem_generator_domain_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:57.163826+00:00
-- url     : https://prove2.me/theorems/6673f9b1-44a8-5330-8a80-4fa6362b3b4a
-- title:
--   Strong Cont Unitary: mem generator domain iff
-- statement:
--   Membership in the generator domain is convergence of the Stone difference quotient.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Generator.lean#L112-L117
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Generator.lean#L112-L117

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Algebra.Star.Unitary
import Definitions.Def_Spectral_Stone_Generator
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open StrongContUnitary

theorem StrongContUnitary.mem_generator_domain_iff (U : StrongContUnitary E) (x : E) :
    x ∈ U.generator.domain ↔
      ∃ y, Filter.Tendsto
        (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x))
        (nhdsWithin 0 {0}ᶜ) (nhds y) := by sorry
