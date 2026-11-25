-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_sum
-- name    : PositivityTheory.Rg.Sw.LC.B1.sf_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:46.926305+00:00
-- url     : https://prove2.me/theorems/69c73c1f-3d7b-4685-abd8-98cdaac3537c
-- title:
--   B1: sf sum
-- statement:
--   The B1 construction uses the sf sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L198-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L198-L204

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
variable (ε : Fin m → Bool)

theorem PositivityTheory.Rg.Sw.LC.B1.sf_sum {ι : Type*} (S : Finset ι) (g : ι → Sym m n) (h : ∀ i ∈ S, SymbolInFirstFamily ε (g i)) : SymbolInFirstFamily ε (∑ i ∈ S, g i) := by sorry
