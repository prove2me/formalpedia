-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPairedPotential_meets
-- name    : ThreeSum.LightTernaryPairedPotential.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:00:49.219919+00:00
-- url     : https://prove2.me/theorems/a574d95d-8227-473d-b9c5-fb9940692f07
-- title:
--   Light Ternary Paired Potential: meets
-- statement:
--   The Light Ternary Paired Potential construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L95-L250
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean#L95-L250

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_meets
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightTernaryPairedPotential.meets (m base Λ colsBase powers : ℕ) (μ : ℕ → ℤ)
    {lim : Limits} {P : Program} {pMain pPowers pRow pDigit pDivide pPoly depth : ℕ}
    (hmain : P[pMain]?=some (body m pPowers pRow pPoly))
    (hPowers : P[pPowers]?=some powTableBody)
    (hRow : P[pRow]?=some (LightWeightRow.body pDigit))
    (hDigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hDivide : P[pDivide]?=some LightSmallDivide.body)
    (hPoly : P[pPoly]?=some (LightTernaryPairedPolynomial.body m))
    (hΛ : 1≤Λ) (hw : (lim.space : ℤ)≤lim.word) (hd : depth+2<lim.depth)
    (hTspace : base+Λ^4≤lim.space) (hCspace : colsBase+width m≤lim.space)
    (hPspace : powers+(width m+1)≤lim.space)
    (hTC : Apart base (Λ^4) colsBase (width m))
    (hTP : Apart base (Λ^4) powers (width m+1))
    (hPC : Apart powers (width m+1) colsBase (width m))
    (U : ℤ) (hU : 0≤U) (hTabs : ∀ k<Λ^4, |μ (base+k)|≤U)
    (hWord : word m Λ U≤lim.word)
    (hPolyWord : (polynomial m).coefficient*(U+1)^(polynomial m).degree≤lim.word) :
    Meets lim P pMain depth [base,Λ,colsBase,powers] μ (time m Λ)
      (fun r ν => r=prefixSum m base Λ μ (Λ^width m) ∧
        (∀ k<Λ^4, ν (base+k)=μ (base+k)) ∧ Kept μ ν (min colsBase powers)) := by sorry
