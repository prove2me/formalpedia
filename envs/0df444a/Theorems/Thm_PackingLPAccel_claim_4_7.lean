-- Prove2me | Theorems.Thm_PackingLPAccel_claim_4_7
-- name    : PackingLPAccel.claim_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:23.996848+00:00
-- url     : https://prove2.me/theorems/d0a08096-5a2e-4534-ba47-c2db9ea375c5
-- title:
--   Claim 4.7 — the potential grows slowly along an update of Algorithm 1
-- statement:
--   For an instance of Problem 4.4 and $\kappa>0$, the iterates of Algorithm 1 stay in $[0,u]$, and for every $y\in[0,u]$ with $y^+$ its update,
--
--   $$P_\kappa(y^+)-P_\kappa(y)\le\frac18\kappa^{-1}a^\top(y^+-y).$$
--
--   Applied to $y=y^{(t)}$ this is display (8). It keeps the penalty terms small until the linear term reaches $\kappa$.
--
--   Differences from the source:
--   - generalization: for the iterates y^{(t)} of Algorithm 1 → for every y ∈ [0,u], together with the iterates staying in [0,u]; reason: the iterates are such points
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Claim 4.7, p.16 (pdf 17), display (8)

import Mathlib
import Definitions.Def_PackingLPAccel_Regression

namespace PackingLPAccel

/-- **Claim 4.7** (manuscript sha256 1dac7711…, p.16). (8) at every `y ∈ [0, u]`, which covers every iterate, and
the iterates of Algorithm 1 stay in `[0, u]`. -/
theorem claim_4_7 {ι : Type*} [Fintype ι] {m₂ mₚ : ℕ} (R : RegInstance ι m₂ mₚ) (_ : R.IsValid)
    (κ : ℝ) (_ : 0 < κ) :
    (∀ t, R.InBox (R.alg1Iter κ t)) ∧
    ∀ y, R.InBox y →
      R.potential κ (R.alg1Step κ y) - R.potential κ y ≤
        (1 / 8) * κ⁻¹ * (R.linTerm (R.alg1Step κ y) - R.linTerm y) := by sorry

end PackingLPAccel
