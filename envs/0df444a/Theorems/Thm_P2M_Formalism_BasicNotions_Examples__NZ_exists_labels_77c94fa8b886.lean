-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_labels_77c94fa8b886
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exists_labels_77c94fa8b886
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:07.987842+00:00
-- url     : https://prove2.me/theorems/b4d15914-2923-4b6e-89ad-6b998b25972d
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exists labels 77c94fa8b886: P2 M Formalism Basic Notions Examples  NZ exists labels 77c94fa8b886
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exists labels 77c94fa8b886 construction uses the P2 M Formalism Basic Notions Examples  NZ exists labels 77c94fa8b886 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L80-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L80-L151

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]

theorem P2M_Formalism_BasicNotions_Examples__NZ_exists_labels_77c94fa8b886 (N p q0 : ℕ) (hp : p.Prime) (h1 : N < 2 * p) (h2 : p + 3 ≤ N) (hq0 : q0.Prime)
    (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1) (hqg : q0 ∣ g - 1) :
    ∃ fA fB q : (ZMod g)[X], LabelOK N fA ∧ LabelOK N fB ∧
      (∀ r : (ZMod g)[X], r ∣ fA → r.natDegree ≠ 0 → N ≤ r.natDegree) ∧
      Irreducible q ∧ q ∣ fB ∧ q.natDegree = p := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exists_labels» := P2M_Formalism_BasicNotions_Examples__NZ_exists_labels_77c94fa8b886
