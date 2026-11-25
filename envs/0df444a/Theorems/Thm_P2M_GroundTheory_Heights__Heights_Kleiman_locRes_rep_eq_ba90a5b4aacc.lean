-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locRes_rep_eq_ba90a5b4aacc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locRes_rep_eq_ba90a5b4aacc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:17.943281+00:00
-- url     : https://prove2.me/theorems/f71c5341-3534-4903-bb5d-bed1323f022e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Res rep eq ba90a5b4aacc: P2 M Ground Theory Heights  Heights Kleiman loc Res rep eq ba90a5b4aacc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Res rep eq ba90a5b4aacc construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Res rep eq ba90a5b4aacc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L96-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L96-L118

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locRes_rep_eq_ba90a5b4aacc {n : ℕ} {z : Ω} {J : Finset (Fin (N + 1))} {a b : Fin (N + 1)}
    (ha : a ∈ J) (hb : b ∈ J) (ga sa gb sb : Poly S N) (ea eb : ℕ)
    (hsa : sa ∈ monos ({a} : Finset (Fin (N + 1)))) (hsb : sb ∈ monos ({b} : Finset (Fin (N + 1))))
    (hsae : sa.IsHomogeneous ea) (hsbe : sb.IsHomogeneous eb)
    (hga : ga.IsHomogeneous (ea + n)) (hgb : gb.IsHomogeneous (eb + n))
    (hza : aeval y ga = z * aeval y sa) (hzb : aeval y gb = z * aeval y sb) :
    locRes (Finset.singleton_subset_iff.mpr ha)
        (LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) ga) ⟨sa, hsa⟩ :
          LocMod S N (Poly S N ⧸ primeOf (S := S) y) {a}) =
      locRes (Finset.singleton_subset_iff.mpr hb)
        (LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) gb) ⟨sb, hsb⟩ :
          LocMod S N (Poly S N ⧸ primeOf (S := S) y) {b}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locRes_rep_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_locRes_rep_eq_ba90a5b4aacc
