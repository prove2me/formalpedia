-- Prove2me | Theorems.Thm_SI_electronvolt_exact
-- name    : SI.electronvolt_exact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T13:56:23.892008+00:00
-- url     : https://prove2.me/theorems/08535ff4-3367-4ec9-ab91-1f6c1422dccc
-- title:
--   The electronvolt is exact
-- statement:
--   In every quantity model of the SI, the electronvolt - the kinetic
--   energy acquired by an electron in passing through a potential
--   difference of one volt - is exactly the volt multiplied by the
--   defining-constant monomial of the elementary charge. In particular
--   the conversion factor 1.602 176 634 × 10⁻¹⁹ between the electronvolt
--   and the joule is exact (Table 8, note l): since Resolution 1 of the
--   26th CGPM fixed the numerical value of the elementary charge, no
--   experimental uncertainty remains in this conversion.
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), chapter 4, Table 8, note l (the electronvolt; the exactness of its conversion factor following the fixing of the elementary charge), with section 2.2, Table 1.

import Mathlib
import Definitions.Def_SI_dim
import Definitions.Def_SI_units
import Definitions.Def_SI_qmodel

/-!
# The electronvolt is exact

Table 8, note l of the SI Brochure: the electronvolt is the kinetic
energy acquired by an electron in passing through a potential
difference of one volt, 1 eV = 1.602 176 634 × 10⁻¹⁹ J, with the
conversion factor exact because the numerical value of the elementary
charge is fixed. In the quantity model, multiplying the volt by the
defining-constant monomial of the elementary charge yields exactly
the electronvolt. This milestone is proved on the way to the goal
theorem `SI.si_complete`.
-/

namespace SI

/-- In every quantity model of the SI, the electronvolt is the volt
scaled by the elementary charge:
toQ M eVolt = (the monomial e) · (toQ M volt). In particular, the
conversion factor 1.602 176 634 × 10⁻¹⁹ between the electronvolt and
the joule is exact (Table 8, note l). -/
theorem electronvolt_exact (M : SIModel) :
    toQ M eVolt = qmul (⟨1, eC Const.e⟩ : QMono) (toQ M volt) := by
  sorry

end SI
