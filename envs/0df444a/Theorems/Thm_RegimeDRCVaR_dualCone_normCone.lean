-- Prove2me | Theorems.Thm_RegimeDRCVaR_dualCone_normCone
-- name    : RegimeDRCVaR.dualCone_normCone
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:36.298933+00:00
-- url     : https://prove2.me/theorems/2633bce3-3750-4707-b87e-6bf561732875
-- title:
--   Proof of Theorem 1 — the dual of the $\ell_m$ norm cone is the $\ell_{m^*}$ norm cone
-- statement:
--   For $m\in[1,+\infty]$ and $\bar K=\{(p;u)\in\mathbb R^{I+1}\mid\|p\|_m\le u\}$,
--   $$
--   \bar K^*=\{(x;\beta)\in\mathbb R^{I+1}\mid\|x\|_{m^*}\le\beta\},
--   $$
--   where $\|\cdot\|_{m^*}$ is the conjugate norm.
--
--   With Lemma EC.2 this turns the semi-infinite constraints of (EC.3) into the bound $\beta_k\ge\|x\|_{m^*}$.
--
--   **Formalization Note** Of the quoted paragraph only its last sentence is a claim; the strict-feasibility remark "$(p/2;u)\succ_{\bar K}0$ for $(p;u)\in\bar K$" fails at $(p;u)=(0;0)$ and is not formalized.
--
--   Differences from the source:
--   - encoding: ℓm norm ‖·‖_m and conjugate norm ‖·‖_{m*} on ℝ^I → normM m (the PiLp m norm on Fin I → ℝ) and normM (ENNReal.conjExponent m); reason: Lean convention; ENNReal.conjExponent sends 1 ↦ ∞, 2 ↦ 2, ∞ ↦ 1, the Hölder conjugate
--   - encoding: ℝ^{I+1} with pairs (p_nk; u_k) → (Fin I → ℝ) × ℝ with inner product y.1 ⬝ z.1 + y.2 z.2; reason: Lean convention; same space
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, proof of Theorem 1, p.ec3 after (EC.6)

import Mathlib
import Definitions.Def_RegimeDRCVaR_dualCone
import Definitions.Def_RegimeDRCVaR_normCone

open scoped ENNReal

namespace RegimeDRCVaR

/-- **The dual of the ℓm norm cone** (Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930,
proof of Theorem 1, p.ec3, after (EC.6)): for `K̄ = {(p; u) ∈ ℝ^{I+1} | ‖p‖_m ≤ u}`,
"It is clear to show `K̄* = {(x; β_k) ∈ ℝ^{I+1} | ‖x‖_{m*} ≤ β_k}`."

**Formalization Note** `m ∈ [1, ∞]` (Theorem 1's range); `‖·‖_{m*}` is
`normM (ENNReal.conjExponent m)`, the conjugate-exponent norm. `ℝ^{I+1}` is `(Fin I → ℝ) × ℝ`. -/
theorem dualCone_normCone {I : ℕ} (m : ℝ≥0∞) (hm : 1 ≤ m) :
    dualCone (normCone (I := I) m) = {y | normM (ENNReal.conjExponent m) y.1 ≤ y.2} := by sorry

end RegimeDRCVaR
