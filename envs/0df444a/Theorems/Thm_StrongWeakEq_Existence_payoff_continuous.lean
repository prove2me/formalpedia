-- Prove2me | Theorems.Thm_StrongWeakEq_Existence_payoff_continuous
-- name    : StrongWeakEq.Existence.payoff_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:53.601986+00:00
-- url     : https://prove2.me/theorems/066fbf20-fae8-4860-9945-8440d2a8f00f
-- title:
--   Proof of Theorem 3.3, p. 26 — continuity of Q ↦ F(Q) = (F(1,Q), …, F(N,Q)) on 𝒬
-- statement:
--   Let $f$ satisfy the standing assumptions (2.1)–(2.3) of §2, and suppose in addition that $q\mapsto f(t,i,q)$ is continuous on $D_i$ for every $t\ge0$ and $i\in S$. Then the map
--   $$\mathcal Q\ni Q\longmapsto F(Q)=\big(F(1,Q),F(2,Q),\dots,F(N,Q)\big)\in\mathbb R^N$$
--   is continuous on $\mathcal Q$.
--
--   This is the analytic core of the existence proof: it gives the joint continuity of $(q,Q)\mapsto f(0,i,q)+F(Q)\cdot q$ (A.25), hence the closed graph of the best-response correspondence.
--
--   **Formalization Note** The paper proves this inside the proof of Theorem 3.3, where the $D_i$ are compact; the statement here does not assume compactness (convergence $Q^n\to Q$ in $\mathcal Q$ already bounds the rows). Continuity of $q\mapsto f(t,i,q)$ on $D_i$ is not among the paper's hypotheses but its proof uses it; without it the statement fails. $\mathbb R^{N\times N}$ carries the product (entrywise) topology. The expectation $\mathbb E_{i,Q}$ over the chain is written out through its one-dimensional marginals: under a generator $Q$ the law of $X_t$ given $X_0=i$ is the $i$-th row of the matrix exponential $e^{tQ}$, so $\mathbb E_{i,Q}[\int_0^\infty \varphi(t,X_t)\,dt]=\int_0^\infty\sum_j (e^{tQ})_{ij}\varphi(t,j)\,dt$ by Fubini; no Markov process is constructed.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 26, proof of Theorem 3.3 (continuity of Q ↦ F(Q))

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model

namespace StrongWeakEq.Existence

/-- Proof of Theorem 3.3, p. 26: `Q ↦ F(Q) = (F(1,Q), …, F(N,Q))` is continuous on `𝒬`, under
(2.1)–(2.3) and continuity of `q ↦ f(t,i,q)` on `Dᵢ` for every `t ≥ 0`. -/
theorem payoff_continuous {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : Standing D f)
    (hcq : ∀ t, 0 ≤ t → ∀ i, ContinuousOn (f t i) (D i)) :
    ContinuousOn (fun Q : Matrix (Fin N) (Fin N) ℝ => fun i => payoff f Q i) (Controls D) := by sorry

end StrongWeakEq.Existence
