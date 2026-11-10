-- Prove2me | Theorems.Thm_RandOrderKnapGAP_Integral_sec_5_gap_in_gpap
-- name    : RandOrderKnapGAP.Integral.sec_5_gap_in_gpap
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:26:59.050004+00:00
-- url     : https://prove2.me/theorems/f41c010a-8e5b-474b-9b3e-8aac8749346b
-- title:
--   §5 — GAP (and knapsack) instances are GPAP instances: resource deletion holds and $\mathrm{OPT}_{\mathrm{int}}$ is preserved
-- statement:
--   Associate one resource with each machine of a GAP instance and represent assigning item $i$ to machine $b$ by an action that consumes $s_{bi}$ units of resource $b$ and nothing of any other resource, with value $v_{bi}$ assigned entirely to resource $b$. If resource $b$ is retained, keep the assignment, otherwise replace it by rejection. This instance satisfies the resource-deletion property (Definition 5.1), and it has the same integral optimum as the GAP instance. Knapsack is the special case of GAP with a single machine: the one-machine GAP instance of a knapsack instance has the same integral optimum.
--
--   This places knapsack and GAP inside GPAP, so a GPAP guarantee applies to both.
--
--   Differences from the source:
--   - reading: 'GAP is a special case of GPAP … This satisfies the above resource-deletion property. Knapsack is then the special case of GAP with a single machine' → ResourceDeletion of toGPAP, OPT_int(toGPAP I) = OPT_int(I), and OPT_int(toGAP K) = OPT_int(K); reason: 'special case' read as: the instance maps preserve the integral optimum; the deletion claim is stated as printed (existence of w and D)
--   - encoding: actions: rejection, or assign to machine b → Fin (m + 1): 0 is rejection, b + 1 assigns to machine b; reason: Lean convention
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), p. 14 (PDF 16), §5

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_Instances

namespace RandOrderKnapGAP.Integral

/-- **§5, p. 14** (GAP is a special case of GPAP): the GPAP instance of a GAP instance (one
resource per machine; assigning `i` to `b` consumes `s_{bi}` of resource `b` only and earns
`v_{bi}`) has the resource-deletion property and the same integral optimum; and a knapsack
instance, as GAP with a single machine, has the same integral optimum. -/
theorem sec_5_gap_in_gpap :
    (∀ (n m : ℕ) (I : GAPInstance n m),
      I.toGPAP.ResourceDeletion ∧ I.toGPAP.OPT = I.OPT) ∧
    (∀ (n : ℕ) (I : KnapsackInstance n), I.toGAP.OPT = I.OPT) := by sorry

end RandOrderKnapGAP.Integral
