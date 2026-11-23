-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_prime_mem_unique_e91ad699f71a
-- name    : P2M_Formalism_BasicNotions_Examples__PlacesToy_prime_mem_unique_e91ad699f71a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:57.369129+00:00
-- url     : https://prove2.me/theorems/dc9a3fd8-7657-485b-b130-c6a2ecc15545
-- title:
--   P2 M Formalism Basic Notions Examples  Places Toy prime mem unique e91ad699f71a: P2 M Formalism Basic Notions Examples  Places Toy prime mem unique e91ad699f71a
-- statement:
--   The P2 M Formalism Basic Notions Examples  Places Toy prime mem unique e91ad699f71a construction uses the P2 M Formalism Basic Notions Examples  Places Toy prime mem unique e91ad699f71a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L148-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L148-L160

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions.Examples₂.PlacesToy
variable {K : Type} [Field K] [NumberField K]
omit [NumberField K]

theorem P2M_Formalism_BasicNotions_Examples__PlacesToy_prime_mem_unique_e91ad699f71a (w : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpw : (p : 𝓞 K) ∈ w.asIdeal) (hqw : (q : 𝓞 K) ∈ w.asIdeal) : p = q := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«PlacesToy».«prime_mem_unique» := P2M_Formalism_BasicNotions_Examples__PlacesToy_prime_mem_unique_e91ad699f71a
