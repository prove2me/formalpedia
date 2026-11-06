-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
-- name    : QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:38:46.5144+00:00
-- url     : https://prove2.me/theorems/d6d0ee3f-5573-491e-ad9b-a6552245de14
-- title:
--   Finite Kraus Family: same Space Knill Laflamme Criterion iff exists indexed scalar
-- statement:
--   The same-space finite-Kraus KL criterion is equivalent to an indexed scalar
--   condition over the original Kraus family. Duplicate operators are handled by
--   choosing representatives from `E.sameSpaceErrorSet`, not by assuming
--   injectivity of `E.operator`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L269-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L269-L278

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    E.sameSpaceKnillLaflammeCriterion C ↔
      ∃ scalar : ι → ι → Complex,
        ∀ i j : ι,
          ∀ x : H, x ∈ C.carrier →
            ∀ y : H, y ∈ C.carrier →
              inner Complex (E.operator i x) (E.operator j y) =
                scalar i j * inner Complex x y := by sorry
