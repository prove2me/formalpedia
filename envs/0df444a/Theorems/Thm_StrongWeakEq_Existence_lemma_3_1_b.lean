-- Prove2me | Theorems.Thm_StrongWeakEq_Existence_lemma_3_1_b
-- name    : StrongWeakEq.Existence.lemma_3_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:23.267974+00:00
-- url     : https://prove2.me/theorems/1e2ab6aa-669b-4e44-9e89-d82577df3fbe
-- title:
--   Lemma 3.1 (3.6), p. 6 — F(i,Q*) − F(i,Q⊗_εQ*) = (Γ^{Q*}(Q*ᵢ) − Γ^{Q*}(Qᵢ))ε + o(ε) under (3.3)–(3.5)
-- statement:
--   Let $f$ satisfy the standing assumptions (2.2)–(2.3) of §2 and the shift bound (3.3)–(3.5): there is a nonnegative $h$ with $|f(t+\varepsilon,i,q)-f(t,i,q)|\le h(t,\varepsilon;i,q)$, nondecreasing in $\varepsilon$ with limit $0$ as $\varepsilon\downarrow0$, and integrable in $t$ for $\varepsilon$ small. Fix $i\in S$ and $Q,Q^*\in\mathcal Q$. Then, as $\varepsilon\downarrow 0$,
--   $$F(i,Q^*)-F(i,Q\otimes_\varepsilon Q^*)=\big(\Gamma^{Q^*}(Q^*_i)-\Gamma^{Q^*}(Q_i)\big)\varepsilon+o(\varepsilon), \tag{3.6}$$
--   where $\Gamma^{Q^*}(Q_i)=f(0,i,Q_i)+Q_i\cdot F(Q^*)$ (3.7).
--
--   The first-order coefficient of the loss from a short deviation is the difference of the gains $\Gamma^{Q^*}$; this is what turns the definition of a weak equilibrium into the pointwise condition of Theorem 3.1.
--
--   **Formalization Note** The $o(\varepsilon)$ is for fixed $(i,Q,Q^*)$, little-o along $\varepsilon\to0^+$. The standing assumption (2.2) is kept alongside (3.3) (the paper says (3.3) "strengthens" it). The expectation $\mathbb E_{i,Q}$ over the chain is written out through its one-dimensional marginals: under a generator $Q$ the law of $X_t$ given $X_0=i$ is the $i$-th row of the matrix exponential $e^{tQ}$, so $\mathbb E_{i,Q}[\int_0^\infty \varphi(t,X_t)\,dt]=\int_0^\infty\sum_j (e^{tQ})_{ij}\varphi(t,j)\,dt$ by Fubini; no Markov process is constructed.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 6, Lemma 3.1, (3.3)–(3.7)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder

namespace StrongWeakEq.Existence

open Filter Topology Asymptotics

/-- Lemma 3.1, (3.6), p. 6: under (2.2)–(2.3) and (3.3)–(3.5), for fixed `i` and `Q, Q* ∈ 𝒬`,
as `ε ↓ 0`, `F(i,Q*) − F(i, Q ⊗_ε Q*) = (Γ^{Q*}(Q*ᵢ) − Γ^{Q*}(Qᵢ)) ε + o(ε)`. -/
theorem lemma_3_1_b {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : Standing D f) (hB : ShiftBound D f)
    (i : Fin N) (Q Qs : Matrix (Fin N) (Fin N) ℝ)
    (hQ : Q ∈ Controls D) (hQs : Qs ∈ Controls D) :
    (fun ε => payoff f Qs i - concatPayoff f ε Q Qs i -
        (Gamma f Qs i (Qs i) - Gamma f Qs i (Q i)) * ε)
      =o[𝓝[>] (0:ℝ)] (fun ε => ε) := by sorry

end StrongWeakEq.Existence
