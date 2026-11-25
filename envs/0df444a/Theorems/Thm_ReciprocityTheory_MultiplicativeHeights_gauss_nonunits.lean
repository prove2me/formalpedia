-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_nonunits
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_nonunits
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:02.175851+00:00
-- url     : https://prove2.me/theorems/8b46ee14-eccb-567f-9caf-7ca756ab6fca
-- title:
--   Multiplicative Heights: gauss nonunits
-- statement:
--   The Multiplicative Heights construction uses the gauss nonunits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValLeIffDivMem.lean#L26-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValLeIffDivMem.lean#L26-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.gauss_nonunits {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] (V : ValuationSubring U)
    (w : Ω) : algebraMap Ω U w ∈ V.nonunits ↔ w ∈ (V.comap (algebraMap Ω U)).nonunits := by sorry
