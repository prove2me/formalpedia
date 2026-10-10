-- Prove2me | Theorems.Thm_StrongWeakEq_Existence_theorem_3_1
-- name    : StrongWeakEq.Existence.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:07.10299+00:00
-- url     : https://prove2.me/theorems/b58f7309-91e4-4b05-b8a5-9df2a4bc4346
-- title:
--   Theorem 3.1, p. 7 — Q* ∈ 𝒬 is a weak equilibrium iff Γ^{Q*}(Q*ᵢ) ≥ Γ^{Q*}(Qᵢ) for all (i,Q) ∈ S × 𝒬
-- statement:
--   Let $f$ satisfy the standing assumptions (2.2)–(2.3) of §2 and the shift bound (3.3)–(3.5). Then $Q^*\in\mathcal Q$ is a weak equilibrium (Definition 2.1) if and only if
--   $$\Gamma^{Q^*}(Q^*_i)\ge\Gamma^{Q^*}(Q_i)\qquad\text{for all }(i,Q)\in S\times\mathcal Q, \tag{3.10}$$
--   where $\Gamma^{Q^*}(Q_i)=f(0,i,Q_i)+Q_i\cdot F(Q^*)$.
--
--   This complete characterization reduces the weak-equilibrium property, defined through a limit, to a family of static inequalities: in each state, the row $Q^*_i$ maximizes $q\mapsto f(0,i,q)+q\cdot F(Q^*)$ over $D_i$.
--
--   **Formalization Note** The paper states "Assume (2.3) and (3.3)"; the standing assumption (2.2) of §2 is also among the hypotheses, as is (2.1) $D_i\subseteq E_i$. The expectation $\mathbb E_{i,Q}$ over the chain is written out through its one-dimensional marginals: under a generator $Q$ the law of $X_t$ given $X_0=i$ is the $i$-th row of the matrix exponential $e^{tQ}$, so $\mathbb E_{i,Q}[\int_0^\infty \varphi(t,X_t)\,dt]=\int_0^\infty\sum_j (e^{tQ})_{ij}\varphi(t,j)\,dt$ by Fubini; no Markov process is constructed.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 7, Theorem 3.1, (3.10)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder

namespace StrongWeakEq.Existence

/-- Theorem 3.1, p. 7: under (2.3) and (3.3) (with the standing assumption (2.2)),
`Q* ∈ 𝒬` is a weak equilibrium iff `Γ^{Q*}(Q*ᵢ) ≥ Γ^{Q*}(Qᵢ)` for all `(i, Q) ∈ S × 𝒬`. -/
theorem theorem_3_1 {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : Standing D f) (hB : ShiftBound D f)
    (Qs : Matrix (Fin N) (Fin N) ℝ) (hQs : Qs ∈ Controls D) :
    IsWeakEquilibrium D f Qs ↔
      ∀ i, ∀ Q ∈ Controls D, Gamma f Qs i (Q i) ≤ Gamma f Qs i (Qs i) := by sorry

end StrongWeakEq.Existence
