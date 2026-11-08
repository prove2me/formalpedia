-- Prove2me | Theorems.Thm_RecoveringBandits_claim_3
-- name    : RecoveringBandits.claim_3
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:55:40.692276+00:00
-- url     : https://prove2.me/theorems/1a1adfd7-d9da-4594-a87c-9541360b5551
-- title:
--   Claim 3 (proof of Lemma 1): $F_i(x)=R_i(d^{(1)}_i)/d^{(1)}_i$ for $x\ge 1/d^{(1)}_i$
-- statement:
--   Let arm $i$ be admissible and $x\ge 1/d^{(1)}_i$. Then for every $T\ge1$,
--
--   $$F_{i,T}(x)\le\frac{R_i(d^{(1)}_i)}{d^{(1)}_i}=F_i(x).$$
--
--   So $F_i$ is constant beyond its first node $1/d^{(1)}_i$: pulling an arm more often than once every $d^{(1)}_i$ periods never increases its long-run average reward.
--
--   Differences from the source:
--   - generalization: x ≥ 1/d^(1)_i within the standing domain x ∈ [0,1] of problem (2) → every real x ≥ 1/d^(1)_i, including x > 1; reason: for x ≥ 1 the budget J ≤ xT is not binding, so F_{i,T}(x) = F_{i,T}(1); the paper's case x ≤ 1 is included
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, proof of Lemma 1, Claim 3, p.ec4 (PDF p.36)

import Mathlib
import Definitions.Def_RecoveringBandits_Admissible
import Definitions.Def_RecoveringBandits_F
import Definitions.Def_RecoveringBandits_supp

namespace RecoveringBandits

/-- **Claim 3 (proof of Lemma 1)**, Simchi-Levi–Zheng–Zhu, arXiv:2106.14813v2, proof of Lemma 1,
Claim 3, p.ec4 (PDF p.36): let `x ≥ 1/d^{(1)}_i`. Then
`F_{i,T}(x) ≤ R_i(d^{(1)}_i)/d^{(1)}_i = F_i(x)` (for every `T ≥ 1`).

**Formalization Note.** Stated for every `x ≥ 1/d^{(1)}_i`, including `x > 1` (outside the
standing domain `[0, 1]` of problem (2)); for `x ≥ 1` the constraint `J ≤ x·T` is not binding, so
this contains the paper's case. -/
theorem claim_3 (r : ℕ → ℝ) (Rmax : ℝ) (hr : ArmAdmissible r Rmax) (x : ℝ)
    (hx : 1 / (supp r 1 : ℝ) ≤ x) :
    (∀ T : ℕ, 1 ≤ T → FT r T x ≤ r (supp r 1) / (supp r 1 : ℝ)) ∧
    F r x = r (supp r 1) / (supp r 1 : ℝ) := by sorry

end RecoveringBandits
