-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_lemma_1
-- name    : OutcomeRebate.Transfer.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:21.272988+00:00
-- url     : https://prove2.me/theorems/8e6c966a-ab10-4e48-9bcc-ba51a6540cc6
-- title:
--   Lemma 1, p. 51 (PDF 52) — 1/z = q iff q ∈ {q0, 1}; otherwise 1/z > q iff q > q0
-- statement:
--   Let $0 < \alpha < 1$, $\lambda \ge 1$ and $q \in (0, 1]$, and put $z = 1 + (\lambda(1-q)/q)^{1/\alpha}$ and $q_0 = 1/(1 + \lambda^{-1/(1-\alpha)})$.
--
--   1. If $q = q_0$ or $q = 1$, then $1/z = q$.
--   2. Otherwise,
--   $$\frac1z > q \iff q > q_0.$$
--
--   Equivalently, the patient's risk premium $qz - 1$ is positive exactly for high-risk drugs. Every comparison between the two pricing systems is decided by this sign.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 51 (PDF 52), Lemma 1

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Lemma 1 (p. 51). Let `0 < α < 1`, `λ ≥ 1` and `q ∈ (0, 1]`. If `q = q₀` or `q = 1`, then
`1/z = q`. Otherwise `1/z > q` iff `q > q₀`. -/
theorem lemma_1 (α lam q : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) (hq : 0 < q ∧ q ≤ 1) :
    ((q = q0 α lam ∨ q = 1) → 1 / zOf α lam q = q) ∧
      (q ≠ q0 α lam → q ≠ 1 → (q < 1 / zOf α lam q ↔ q0 α lam < q)) := by sorry

end OutcomeRebate.Transfer
