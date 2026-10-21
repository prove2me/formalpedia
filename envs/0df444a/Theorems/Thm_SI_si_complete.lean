-- Prove2me | Theorems.Thm_SI_si_complete
-- name    : SI.si_complete
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-20T13:58:29.490954+00:00
-- url     : https://prove2.me/theorems/6a6cb1b8-9734-4610-92bc-7b7776614746
-- title:
--   The SI is determined by its seven exact defining constants
-- statement:
--   The goal of the mission. For every quantity model of the SI whose
--   dimension map is bijective: the seven base units are the exact
--   inversions of section 2.3.1; all 29 named units of the SI (the seven
--   base units and the 22 units with special names) are coherent; the
--   electronvolt is exactly the volt times the elementary charge; and the
--   identification of coherent units with defining-constant monomials is
--   faithful. Together with the printed-approximation milestone, this
--   states that the International System of Units is determined, exactly
--   and checkably, by the seven exact defining constants of Table 1, the
--   decimal prefixes of chapter 3, and the exact non-SI conversions of
--   Table 8.
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), section 2.2 (the definition of the SI by seven defining constants), sections 2.3.1 and 2.3.4, chapter 3, and chapter 4, Table 8.

import Mathlib
import Definitions.Def_SI_dim
import Definitions.Def_SI_units
import Definitions.Def_SI_qmodel

/-!
# The SI is determined by its seven exact defining constants

The goal of the mission. Section 2.2 of the SI Brochure: the SI is
defined by fixing the exact numerical values of seven defining
constants (Table 1); section 2.3.4: every unit of the SI is either one
of the seven base units or is a coherent derived unit, a product of
powers of the base units with numerical factor one. The goal theorem
combines the milestones: the defining constants span the dimensions
of the SI (`SI.dim_basis`), the seven base units are their exact
inversions (`SI.base_unit_inversions`), all 29 named units are
coherent (`SI.coherent_derived_22`), the electronvolt conversion is
exact (`SI.electronvolt_exact`), and the identification of coherent
units with defining-constant monomials is faithful
(`SI.model_faithful`). Together these state that the International
System of Units is determined, up to the printed decimal
approximations of `SI.printed_approximations`, by the seven exact
defining constants and the decimal prefixes.
-/

namespace SI

/-- The SI is determined by its seven exact defining constants: the
dimension map of the defining constants is bijective, the seven base
units are the exact inversions of section 2.3.1, all 29 named SI
units are coherent, the electronvolt is the volt times the elementary
charge exactly, and the identification of coherent units with
defining-constant monomials is faithful. -/
theorem si_complete (M : SIModel)
    (hbas : Function.Bijective dimOfExpo) :
    toQ M second = sMono ∧
    toQ M metre = mMono ∧
    toQ M kilogram = kgMono ∧
    toQ M ampere = AMono ∧
    toQ M kelvin = KMono ∧
    toQ M mole = molMono ∧
    toQ M candela = cdMono ∧
    (∀ u ∈ named29, IsCoherent u) ∧
    toQ M eVolt = qmul (⟨1, eC Const.e⟩ : QMono) (toQ M volt) ∧
    ∀ u v : SIUnit, IsCoherent u → IsCoherent v →
      toQ M u = toQ M v → u = v := by
  sorry

end SI
