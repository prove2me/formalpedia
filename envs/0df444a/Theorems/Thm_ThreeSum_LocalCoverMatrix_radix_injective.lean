-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverMatrix_radix_injective
-- name    : ThreeSum.LocalCoverMatrix.radix_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:37.447337+00:00
-- url     : https://prove2.me/theorems/f37a699e-1241-477c-bcf0-f5483e5b59d7
-- title:
--   Local Cover Matrix: radix injective
-- statement:
--   The Local Cover Matrix construction uses the radix injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverMatrix.lean#L44-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalCoverMatrix.lean#L44-L47

import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverMatrix
open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes
variable {h L k : ℕ}

theorem ThreeSum.LocalCoverMatrix.radix_injective {p a b c e : ℕ} (hb : b < p) (he : e < p)
    (hh : a*p+b=c*p+e) : a=c ∧ b=e := by sorry
