-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeScales_physical_false_mass_le
-- name    : ThreeSum.BandPrimeScales.physical_false_mass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:18.451442+00:00
-- url     : https://prove2.me/theorems/105df637-918f-4535-ad7e-0c26470ceed9
-- title:
--   Band Prime Scales: physical false mass le
-- statement:
--   The concrete owner-domain false mass has the existing subquadratic
--   majorant; the baseline uses the quadratic owner catalog and cubic band size.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeScales.lean#L104-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeScales.lean#L104-L115

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

theorem ThreeSum.BandPrimeScales.physical_false_mass_le {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hcount : rs.length ≤ 3*bandCount n^2)
    (hbudget : divisorBudget k n*primeWindow n ≤
      candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    (physicalMass n (modulus n nA nB nC A B C rs) nA nB nC A B C rs : ℝ) ≤
      MassScales.falseMajorant k n := by sorry
