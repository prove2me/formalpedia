-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_errorWordProbability_eq_hammingWeight
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.errorWordProbability_eq_hammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:33:29.754424+00:00
-- url     : https://prove2.me/theorems/0d2f5e9b-e469-42ad-81b7-e9c9ffef5e1a
-- title:
--   BH12 Noisy Injection: error Word Probability eq hamming Weight
-- statement:
--   The independent physical word law is the Bernoulli monomial determined by
--   the literal Hamming support, rather than a stored weight-enumerator value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L654-L694
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L654-L694

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12NoisyInjection
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.errorWordProbability_eq_hammingWeight (p : ErrorParameter)
    (error : Word (ZMod 2) Index) :
    errorWordProbability p error =
      p.rate ^ HammingWeight error *
        p.cleanWeight ^ (Fintype.card Index - HammingWeight error) := by sorry
