-- Prove2me | Theorems.Thm_RobustSDP_Structured_full_scaling_set
-- name    : RobustSDP.Structured.full_scaling_set
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:02:09.287228+00:00
-- url     : https://prove2.me/theorems/46ca8127-0720-4f19-98e2-f6e9991f80de
-- title:
--   The scaling set 𝓑 for full perturbations consists of the triples (τI, τI, 0)
-- statement:
--   Let $p, q \ge 1$ and take the full perturbation space $\mathcal{D} = \mathbb{R}^{p\times q}$. Let $\mathcal{B}$ be the scaling set of $\mathcal{D}$: the triples $(S,T,G) \in \mathbb{R}^{p\times p}\times\mathbb{R}^{q\times q}\times\mathbb{R}^{p\times q}$ with $S\Delta = \Delta T$ and $G\Delta^T = -\Delta G^T$ for every $\Delta \in \mathcal{D}$. Then
--
--   1. $(S,T,G) \in \mathcal{B}$ if and only if there is a scalar $\tau$ with
--   $$S = \tau I_p, \qquad T = \tau I_q, \qquad G = 0;$$
--   2. if moreover $S \succeq 0$, the scalar satisfies $\tau \ge 0$.
--
--   This is the remark on p. 37 that, in the full case, the scaling variables of Theorem 3.2 collapse to the single multiplier $\tau$ of Section 3.1, so that the structured SDP reduces to the full-perturbation SDP.
--
--   **Formalization Note** $\mathcal{D}$ is the top submodule `⊤`. The hypotheses $p, q \ge 1$ are needed: for $p = 0$ the condition on $T$ is vacuous, and for $q = 0$ the condition on $S$ is. The sign $\tau \ge 0$ does not follow from membership in $\mathcal{B}$ alone; it is stated under $S \succeq 0$ (`Matrix.PosSemidef`), the constraint the SDP imposes. The paper's closing sentence "We then recover the exact results of section 3.1" is not part of this statement.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 37, §3.2, paragraph after Theorem 3.2 (with Eq. (11), corrected)

import Mathlib
import Definitions.Def_RobustSDP_Structured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

/-- The full-perturbation case of `𝓑`, p. 37 (paragraph after Theorem 3.2): when `𝒟 = ℝ^{p×q}`
(with `p, q ≥ 1`), a triple `(S, T, G)` lies in the (corrected) scaling set `𝓑` iff `G = 0` and
`S = τ I_p`, `T = τ I_q` for one scalar `τ`; if moreover `S ⪰ 0`, then `τ ≥ 0`. -/
theorem full_scaling_set {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ) :
    ((S, T, G) ∈ scalingSet (⊤ : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) ↔
        ∃ τ : ℝ, S = τ • (1 : Matrix (Fin p) (Fin p) ℝ) ∧ T = τ • (1 : Matrix (Fin q) (Fin q) ℝ) ∧
          G = 0) ∧
      (S.PosSemidef → (S, T, G) ∈ scalingSet (⊤ : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) →
        ∃ τ : ℝ, 0 ≤ τ ∧ S = τ • (1 : Matrix (Fin p) (Fin p) ℝ) ∧
          T = τ • (1 : Matrix (Fin q) (Fin q) ℝ) ∧ G = 0) := by sorry

end RobustSDP.Structured
