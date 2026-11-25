-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_multiset_sum_pow_eq
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.multiset_sum_pow_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:44.442855+00:00
-- url     : https://prove2.me/theorems/50c3deae-3f3a-4e93-a9be-8e0d28129771
-- title:
--   Fib: multiset sum pow eq
-- statement:
--   The Fib construction uses the multiset sum pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean#L32-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.multiset_sum_pow_eq {S : Type*} [CommRing S] (s : Multiset S) {n : ℕ}
    (hn : Multiset.card s = n) (k : ℕ) :
    (s.map (· ^ k)).sum = aeval (fun i : Fin n => s.esymm (i + 1)) (psumQ n k) := by sorry
