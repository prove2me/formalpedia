-- Prove2me | Theorems.Thm_UpperTheory_Ram_Fun_coprime_condN_of_splitK
-- name    : UpperTheory.Ram.Fun.coprime_condN_of_splitK
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:22.993354+00:00
-- url     : https://prove2.me/theorems/af481d85-6c0a-54d4-99f2-9a5801279b7c
-- title:
--   Fun: coprime cond N of split K
-- statement:
--   The Fun construction uses the coprime cond N of split K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean#L79-L80

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
noncomputable section
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Fun
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)

theorem UpperTheory.Ram.Fun.coprime_condN_of_splitK {p : ℕ} (hp : p.Prime) (h : H.cls p = .splitK) : Nat.Coprime p (H.QS * H.q * H.d) := by sorry
