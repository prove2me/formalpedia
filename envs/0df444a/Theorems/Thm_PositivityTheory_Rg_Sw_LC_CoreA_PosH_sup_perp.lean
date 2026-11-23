-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreA_PosH_sup_perp
-- name    : PositivityTheory.Rg.Sw.LC.CoreA.PosH.sup_perp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:47.306854+00:00
-- url     : https://prove2.me/theorems/0063cc22-51ed-4173-b422-3c80a262baac
-- title:
--   Pos H: sup perp
-- statement:
--   The Pos H construction uses the sup perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SupPerp.lean#L16-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SupPerp.lean#L16-L43

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SupPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreA
variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}
open PositivityTheory.Rg.Sw.LC.CoreA.PosH
variable (h : PosH φ)
include h

theorem PositivityTheory.Rg.Sw.LC.CoreA.PosH.sup_perp [FiniteDimensional ℂ V] (W : Submodule ℂ V) : W ⊔ h.perp W = ⊤ := by sorry
