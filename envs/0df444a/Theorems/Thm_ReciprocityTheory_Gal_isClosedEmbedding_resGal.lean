-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_isClosedEmbedding_resGal
-- name    : ReciprocityTheory.Gal.isClosedEmbedding_resGal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:30.39652+00:00
-- url     : https://prove2.me/theorems/89c49a27-cf15-5dbc-8284-da70dc22829c
-- title:
--   Gal: is Closed Embedding res Gal
-- statement:
--   The Gal construction uses the is Closed Embedding res Gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalEA.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalEA.lean#L51-L55

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_Hypotheses_Descent
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalEA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp
variable {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω]

theorem ReciprocityTheory.Gal.isClosedEmbedding_resGal [IsAlgClosure F Ω] [CharZero L] :
    Topology.IsClosedEmbedding (resGal F L Ω) := by sorry
