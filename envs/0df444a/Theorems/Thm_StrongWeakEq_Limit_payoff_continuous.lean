-- Prove2me | Theorems.Thm_StrongWeakEq_Limit_payoff_continuous
-- name    : StrongWeakEq.Limit.payoff_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:12.161661+00:00
-- url     : https://prove2.me/theorems/9e85b83f-3dd2-42e7-af18-dc8574a15248
-- title:
--   Proof of Theorem 3.3, p. 26 — the payoff vector Q ↦ F(Q) = (F(1,Q), …, F(N,Q)) is continuous on 𝒬
-- statement:
--   Consider the continuous-time model of §2 under the standing assumptions (2.1)–(2.3), and assume in addition that $q\mapsto f(t,i,q)$ is continuous on $D_i$ for every $t\ge0$ and $i\in S$. Then the map
--
--   $$
--   \mathcal Q\ni Q\ \longmapsto\ F(Q)=\big(F(1,Q),F(2,Q),\dots,F(N,Q)\big)\in\mathbb R^N
--   $$
--
--   is continuous on $\mathcal Q$ (with the product topology on $\mathbb R^{N\times N}$), where $F(i,Q)=\mathbb E_{i,Q}\big[\int_0^\infty f(t,X_t,Q_{X_t})\,dt\big]$ is the expected payoff (2.4).
--
--   In the paper this continuity is established inside the proof of Theorem 3.3 (to obtain the upper semicontinuity of the best-response map), and it is reused in the proof of Lemma 5.1 for the term comparing the payoffs of $Q^n$ and of their limit $Q^*$.
--
--   **Formalization Note** The paper proves this for compact $D_i$; no compactness is assumed here, since the statement concerns convergent sequences in $\mathcal Q$, whose rows are bounded. The continuity of $f(t,i,\cdot)$ on $D_i$ is the hypothesis the argument needs; in the setting of Theorem 5.2 it follows from the joint continuity of $f(\cdot,i,\cdot)$. $F(i,Q)$ is written as $\int_0^\infty\sum_j(e^{tQ})_{ij}f(t,j,Q_j)\,dt$ (Fubini and the marginals of the chain). States are `Fin N`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 26, proof of Theorem 3.3

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model

namespace StrongWeakEq.Limit

/-- Proof of Theorem 3.3, p. 26: `Q ↦ F(Q) = (F(1,Q), …, F(N,Q))` is continuous on `𝒬`, under
(2.1)–(2.3) and continuity of `q ↦ f(t,i,q)` on `Dᵢ` for every `t ≥ 0`. -/
theorem payoff_continuous {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : StrongWeakEq.Existence.Standing D f)
    (hcq : ∀ t, 0 ≤ t → ∀ i, ContinuousOn (f t i) (D i)) :
    ContinuousOn (fun Q : Matrix (Fin N) (Fin N) ℝ => fun i => StrongWeakEq.Existence.payoff f Q i) (StrongWeakEq.Existence.Controls D) := by sorry

end StrongWeakEq.Limit
