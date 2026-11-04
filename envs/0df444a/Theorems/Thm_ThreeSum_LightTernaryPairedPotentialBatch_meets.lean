-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotentialBatch_meets
-- name    : ThreeSum.LightTernaryPairedPotentialBatch.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:58.01253+00:00
-- url     : https://prove2.me/theorems/41e1de56-84e7-4f4a-8b96-bbe44a7795be
-- title:
--   Light Ternary Paired Potential Batch: meets
-- statement:
--   The Light Ternary Paired Potential Batch construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotentialBatch.lean#L27-L155
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotentialBatch.lean#L27-L155

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_meets
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotentialBatch
open Light LightTernaryPairedPotential
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.LightTernaryPairedPotentialBatch.meets {lim : Limits} {P : Program} {pMain pPotential pPowers pRow pDigit pDivide pPoly d : ℕ}
    (K base Λ H cols powers cutoff : ℕ) (μ : ℕ→ℤ)
    (hmain : P[pMain]?=some (body pPotential))
    (hPotential : P[pPotential]?=some (LightTernaryPairedPotential.body K pPowers pRow pPoly))
    (hPowers : P[pPowers]?=some powTableBody)
    (hRow : P[pRow]?=some (LightWeightRow.body pDigit))
    (hDigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hDivide : P[pDivide]?=some LightSmallDivide.body)
    (hPoly : P[pPoly]?=some (LightTernaryPairedPolynomial.body K))
    (hΛ : 1≤Λ) (hw : (lim.space : ℤ)≤lim.word) (hd : d+3<lim.depth)
    (hcut : base+H*Λ^4≤cutoff) (hcutSpace : cutoff≤lim.space)
    (hcols : cols+TernaryPairedColumnEnumeration.width K≤lim.space)
    (hpowers : powers+(TernaryPairedColumnEnumeration.width K+1)≤lim.space)
    (hcutCols : cutoff≤cols) (hcutPowers : cutoff≤powers)
    (hApart : Apart powers (TernaryPairedColumnEnumeration.width K+1) cols (TernaryPairedColumnEnumeration.width K))
    (U : ℤ) (hU : 0≤U) (hread : ∀ i<H, ∀ q<Λ^4, |μ (base+i*Λ^4+q)|≤U)
    (hKernelWord : LightTernaryPairedPotential.word K Λ U≤lim.word)
    (hPolyWord : (LightTernaryPairedPolynomial.polynomial K).coefficient*
      (U+1)^(LightTernaryPairedPolynomial.polynomial K).degree≤lim.word)
    (hSumWord : (H : ℤ)*(Λ^TernaryPairedColumnEnumeration.width K : ℕ)*
      (LightTernaryPairedPolynomial.polynomial K).bound U≤lim.word)
    (hHword : (H : ℤ)≤lim.word) :
    Meets lim P pMain d [base,Λ,H,cols,powers] μ (time K Λ H)
      (fun r ν => r=total K base Λ μ H ∧ Kept μ ν cutoff) := by sorry
