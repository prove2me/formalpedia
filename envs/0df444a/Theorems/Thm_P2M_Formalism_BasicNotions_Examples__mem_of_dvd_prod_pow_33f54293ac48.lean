-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__mem_of_dvd_prod_pow_33f54293ac48
-- name    : P2M_Formalism_BasicNotions_Examples__mem_of_dvd_prod_pow_33f54293ac48
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:13.719658+00:00
-- url     : https://prove2.me/theorems/21ce81c0-4710-455d-9633-146f32b18ab2
-- title:
--   P2 M Formalism Basic Notions Examples  mem of dvd prod pow 33f54293ac48: P2 M Formalism Basic Notions Examples  mem of dvd prod pow 33f54293ac48
-- statement:
--   The P2 M Formalism Basic Notions Examples  mem of dvd prod pow 33f54293ac48 construction uses the P2 M Formalism Basic Notions Examples  mem of dvd prod pow 33f54293ac48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L6-L10

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Primes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂

theorem P2M_Formalism_BasicNotions_Examples__mem_of_dvd_prod_pow_33f54293ac48 {l : ℕ} (hl : l.Prime) (ps : List ℕ) (K : ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (h : l ∣ ps.prod ^ K) : l ∈ ps := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«mem_of_dvd_prod_pow» := P2M_Formalism_BasicNotions_Examples__mem_of_dvd_prod_pow_33f54293ac48
