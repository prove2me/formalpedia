-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermitian_lattice_pairing_duality
-- name    : ReciprocityTheory.ChartRestriction.G.FD.hermitian_lattice_pairing_duality
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:21.71431+00:00
-- url     : https://prove2.me/theorems/27d4e0be-78e0-4ea3-b114-9a667f37f583
-- title:
--   FD: hermitian lattice pairing duality
-- statement:
--   The FD construction uses the hermitian lattice pairing duality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPairingAlgebra.lean#L71-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPairingAlgebra.lean#L71-L138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open HermitianPairingAlgebra

theorem ReciprocityTheory.ChartRestriction.G.FD.hermitian_lattice_pairing_duality : PerpQuotientSelfDual (E := E) := by sorry
