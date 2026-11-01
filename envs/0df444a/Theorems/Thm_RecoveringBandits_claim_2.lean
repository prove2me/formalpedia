-- Prove2me | Theorems.Thm_RecoveringBandits_claim_2
-- name    : RecoveringBandits.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:24.100404+00:00
-- url     : https://prove2.me/theorems/ab256e60-c89b-4950-80bb-f165b7f7edc0
-- title:
--   Claim 2 (proof of Lemma 1): on $[1/(d+1),1/d]$, $F_i$ is the interpolation of $R^{cc}_i(d)/d$
-- statement:
--   Let arm $i$ be admissible, $d$ a positive integer with $d\ge d^{(1)}_i$, $\alpha\in(0,1]$, and
--
--   $$x=\alpha\,\frac1{d+1}+(1-\alpha)\,\frac1d .$$
--
--   Then for every $T\ge1$,
--
--   $$F^{cc}_{i,T}(x)\le \alpha\,\frac{R^{cc}_i(d+1)}{d+1}+(1-\alpha)\,\frac{R^{cc}_i(d)}{d}=F_i(x),$$
--
--   where $F^{cc}_{i,T}$ is the value of problem (2) with $R_i$ replaced by its upper concave envelope $R^{cc}_i$, and $F_i$ is the long-run value of the arm itself.
--
--   Together with Claim 3 this determines $F_i$ on $(0,1]$ and gives the bound $F_{i,T}\le F^{cc}_{i,T}\le F_i$ of Lemma 1.
--
--   Differences from the source:
--   - encoding: F^cc_{i,T}(x), the value of (EC.1) → FT (Rcc r) T x; reason: (EC.1) is problem (2) for R^cc_i; same instances
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, proof of Lemma 1, Claim 2, pp.ec2–ec3 (PDF pp.34–35)

import Mathlib
import Definitions.Def_RecoveringBandits_Admissible
import Definitions.Def_RecoveringBandits_F
import Definitions.Def_RecoveringBandits_supp
import Definitions.Def_RecoveringBandits_Rcc

namespace RecoveringBandits

/-- **Claim 2 (proof of Lemma 1)**, Simchi-Levi–Zheng–Zhu, arXiv:2106.14813v2, proof of Lemma 1,
Claim 2, pp.ec2–ec3 (PDF pp.34–35): let `x = α·1/(d+1) + (1 − α)·1/d` with `d ∈ ℤ₊`,
`d ≥ d^{(1)}_i` and `α ∈ (0, 1]`. Then `F^cc_{i,T}(x) ≤ α R^cc_i(d+1)/(d+1) + (1 − α) R^cc_i(d)/d
= F_i(x)`, for every `T ≥ 1`.

**Formalization Note.** `F^cc_{i,T}` of (EC.1) is `FT (Rcc r)`; `F_i` is `F r`, the limsup of
problem (2) for the arm's own rewards. -/
theorem claim_2 (r : ℕ → ℝ) (Rmax : ℝ) (hr : ArmAdmissible r Rmax) (d : ℕ) (hd1 : 1 ≤ d)
    (hd : supp r 1 ≤ d) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∀ T : ℕ, 1 ≤ T →
      FT (Rcc r) T (α * (1 / ((d : ℝ) + 1)) + (1 - α) * (1 / (d : ℝ))) ≤
        α * (Rcc r (d + 1) / ((d : ℝ) + 1)) + (1 - α) * (Rcc r d / (d : ℝ))) ∧
    F r (α * (1 / ((d : ℝ) + 1)) + (1 - α) * (1 / (d : ℝ))) =
      α * (Rcc r (d + 1) / ((d : ℝ) + 1)) + (1 - α) * (Rcc r d / (d : ℝ)) := by sorry

end RecoveringBandits
