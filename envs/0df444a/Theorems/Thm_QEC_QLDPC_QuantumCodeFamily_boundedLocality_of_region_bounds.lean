-- Prove2me | Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_boundedLocality_of_region_bounds
-- name    : QEC.QLDPC.QuantumCodeFamily.boundedLocality_of_region_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:55.473038+00:00
-- url     : https://prove2.me/theorems/fd10c420-f36a-4fa3-92f1-465beea9d23b
-- title:
--   Quantum Code Family: bounded Locality of region bounds
-- statement:
--   Concrete row and column bounds imply the indexed locality bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L100-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L100-L107

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_boundedLocality_of_region_bounds

set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.QuantumCodeFamily.boundedLocality_of_region_bounds
    (F : QuantumCodeFamily A ι κ) (a : A) {bound : Nat}
    (hcheck : ∀ checkIndex,
      ((F.presentation a).checks checkIndex).region.selected.card ≤ bound)
    (hcoordinate : ∀ coordinate,
      ((F.presentation a).incidence.variableSupport coordinate).card ≤ bound) :
    Coding.BoundedLocality (F.localityProfile a) bound := by sorry
