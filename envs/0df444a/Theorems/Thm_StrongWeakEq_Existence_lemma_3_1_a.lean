-- Prove2me | Theorems.Thm_StrongWeakEq_Existence_lemma_3_1_a
-- name    : StrongWeakEq.Existence.lemma_3_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:39.501197+00:00
-- url     : https://prove2.me/theorems/6e026d0f-f102-4a93-a554-2ea4ee3e9647
-- title:
--   Lemma 3.1 (3.2), p. 6 — F(i, Q⊗_εQ*) = F_ε(i,Q*) + [f(0,i,Qᵢ) + F_ε(Q*)·Qᵢ]ε + o(ε)
-- statement:
--   Let $f$ satisfy the standing assumptions (2.2)–(2.3) of §2, fix a state $i\in S$ and two admissible generators $Q,Q^*\in\mathcal Q$. Write $F_\varepsilon(Q^*)=(F_\varepsilon(1,Q^*),\dots,F_\varepsilon(N,Q^*))$ for the shifted payoff (3.1). Then, as $\varepsilon\downarrow0$,
--   $$F(i,Q\otimes_\varepsilon Q^*)=F_\varepsilon(i,Q^*)+\big[f(0,i,Q_i)+F_\varepsilon(Q^*)\cdot Q_i\big]\varepsilon+o(\varepsilon). \tag{3.2}$$
--
--   This is the first-order expansion of the payoff of a short deviation to $Q$ on $[0,\varepsilon]$, expressed through the payoff of the continuation $Q^*$ seen from time $\varepsilon$.
--
--   **Formalization Note** The $o(\varepsilon)$ is for fixed $(i,Q,Q^*)$ and is stated as little-o along $\varepsilon\to0^+$ of the difference of the two sides. The expectation $\mathbb E_{i,Q}$ over the chain is written out through its one-dimensional marginals: under a generator $Q$ the law of $X_t$ given $X_0=i$ is the $i$-th row of the matrix exponential $e^{tQ}$, so $\mathbb E_{i,Q}[\int_0^\infty \varphi(t,X_t)\,dt]=\int_0^\infty\sum_j (e^{tQ})_{ij}\varphi(t,j)\,dt$ by Fubini; no Markov process is constructed.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 6, Lemma 3.1, (3.2)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model

namespace StrongWeakEq.Existence

open Filter Topology Asymptotics

/-- Lemma 3.1, (3.2), p. 6: under (2.2)–(2.3), for fixed `i` and `Q, Q* ∈ 𝒬`, as `ε ↓ 0`,
`F(i, Q ⊗_ε Q*) = F_ε(i,Q*) + [f(0,i,Qᵢ) + F_ε(Q*) · Qᵢ] ε + o(ε)`. -/
theorem lemma_3_1_a {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : Standing D f)
    (i : Fin N) (Q Qs : Matrix (Fin N) (Fin N) ℝ)
    (hQ : Q ∈ Controls D) (hQs : Qs ∈ Controls D) :
    (fun ε => concatPayoff f ε Q Qs i -
        (shiftedPayoff f ε Qs i +
          (f 0 i (Q i) + (fun j => shiftedPayoff f ε Qs j) ⬝ᵥ Q i) * ε))
      =o[𝓝[>] (0:ℝ)] (fun ε => ε) := by sorry

end StrongWeakEq.Existence
