-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_good_8aff834fa90b
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exists_good_8aff834fa90b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:44.974951+00:00
-- url     : https://prove2.me/theorems/569ebfa2-b227-4254-a621-dce1b3ac2184
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exists good 8aff834fa90b: P2 M Formalism Basic Notions Examples  NZ exists good 8aff834fa90b
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exists good 8aff834fa90b construction uses the P2 M Formalism Basic Notions Examples  NZ exists good 8aff834fa90b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L153-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L153-L173

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_exists_good_8aff834fa90b (N p q0 : ℕ) (hp : p.Prime) (h1 : N < 2 * p) (h2 : p + 3 ≤ N) (hq0 : q0.Prime)
    (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1) (hqg : q0 ∣ g - 1) :
    ∃ fA fB : (ZMod g)[X], fA ≠ fB ∧ (fA.Monic ∧ fA.natDegree = N ∧ fA.coeff 0 ≠ 0) ∧
      (fB.Monic ∧ fB.natDegree = N ∧ fB.coeff 0 ≠ 0) ∧
      ∀ (PP J : Type) (t : PP → Bool), (∃ v, t v = true) → (∃ v, t v = false) →
        IsGood N g (fun v => if t v then fA else fB) (fun (_ : PP) (_ : J) => (1 : (ZMod g)ˣ)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exists_good» := P2M_Formalism_BasicNotions_Examples__NZ_exists_good_8aff834fa90b
