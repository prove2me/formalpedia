-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_evW_factor
-- name    : ReciprocityTheory.ChartRestriction.G.T0.evW_factor
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:09:10.770378+00:00
-- url     : https://prove2.me/theorems/707cd746-1051-5611-a3cf-b89c85f9e059
-- title:
--   T0: ev W factor
-- statement:
--   The T0 construction uses the ev W factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffEvWMem.lean#L117-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffEvWMem.lean#L117-L138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SumLeSqrtCardMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial

theorem ReciprocityTheory.ChartRestriction.G.T0.evW_factor {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S]
    [Algebra R B] [Algebra S B] [IsScalarTower R S B] {D N n : ℕ} (y : Fin (N + 1) → S) (w0 : B)
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) :
    evW (fun j => algebraMap S B (y j) * w0) Q =
      MvPolynomial.map (algebraMap S B) (evW y Q) * C (w0 ^ n) := by sorry
