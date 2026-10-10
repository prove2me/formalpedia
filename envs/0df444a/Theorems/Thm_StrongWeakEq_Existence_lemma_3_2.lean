-- Prove2me | Theorems.Thm_StrongWeakEq_Existence_lemma_3_2
-- name    : StrongWeakEq.Existence.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:16.852451+00:00
-- url     : https://prove2.me/theorems/c4d45b1f-1c6e-4cc2-ac75-6e2c15c7b35b
-- title:
--   Lemma 3.2, p. 8 — second-order expansion (3.16) of F(i,Q*) − F(i,Q⊗_εQ*) with the coefficient Λ (3.17)
-- statement:
--   Let $f$ satisfy the standing assumptions (2.1)–(2.3) of §2, let $f(\cdot,i,q)$ be $C^1$ on $[0,\infty)$ for all $i\in S$ and $q\in D_i$ with derivative $f_t$, let $f_t$ also satisfy (2.3), and let $r$ be a function, continuous in $\varepsilon$, with
--   $$|f(t+\varepsilon,i,q)-(f(t,i,q)+\varepsilon f_t(t,i,q))|\le r(t,\varepsilon;i,q)\qquad t\ge0,\ \varepsilon>0,\ i\in S,\ q\in D_i, \tag{3.14}$$
--   satisfying (3.5) and with $r(t,\varepsilon;i,q)/\varepsilon$ nondecreasing in $\varepsilon$ (3.15). Then, for any $i\in S$ and $Q,Q^*\in\mathcal Q$, as $\varepsilon\downarrow0$,
--   $$F(i,Q^*)-F(i,Q\otimes_\varepsilon Q^*)=\big(\Gamma^{Q^*}(Q^*_i)-\Gamma^{Q^*}(Q_i)\big)\varepsilon+\tfrac12\big(\Lambda^{Q^*}(i,Q^*)-\Lambda^{Q^*}(i,Q)\big)\varepsilon^2+o(\varepsilon^2), \tag{3.16}$$
--   where $\Lambda^{Q^*}(i,Q)=f_t(0,i,Q_i)+Q_i\cdot\big(2G(Q^*)+\Gamma^{Q^*}(Q)\big)$ (3.17) and $G(Q)$ is the vector of expected payoffs of $f_t$.
--
--   The second-order term decides whether a deviation pays when the first-order term vanishes; it underlies Propositions 3.2 and 3.3.
--
--   **Formalization Note** $f_t$ is a parameter tied to $f$ by a one-sided derivative condition on $[0,\infty)$ (see the definition `SecondOrderReg`). The $o(\varepsilon^2)$ is for fixed $(i,Q,Q^*)$, little-o along $\varepsilon\to0^+$. The expectation $\mathbb E_{i,Q}$ over the chain is written out through its one-dimensional marginals: under a generator $Q$ the law of $X_t$ given $X_0=i$ is the $i$-th row of the matrix exponential $e^{tQ}$, so $\mathbb E_{i,Q}[\int_0^\infty \varphi(t,X_t)\,dt]=\int_0^\infty\sum_j (e^{tQ})_{ij}\varphi(t,j)\,dt$ by Fubini; no Markov process is constructed.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 8, Lemma 3.2, (3.14)–(3.17)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder

namespace StrongWeakEq.Existence

open Filter Topology Asymptotics

/-- Lemma 3.2, (3.16), p. 8: under (2.3) and the conditions of Lemma 3.2, for `i ∈ S` and
`Q, Q* ∈ 𝒬`, as `ε ↓ 0`,
`F(i,Q*) − F(i, Q ⊗_ε Q*) = (Γ^{Q*}(Q*ᵢ) − Γ^{Q*}(Qᵢ)) ε + ½ (Λ^{Q*}(i,Q*) − Λ^{Q*}(i,Q)) ε² + o(ε²)`. -/
theorem lemma_3_2 {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f ft : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : Standing D f) (hR : SecondOrderReg D f ft)
    (i : Fin N) (Q Qs : Matrix (Fin N) (Fin N) ℝ)
    (hQ : Q ∈ Controls D) (hQs : Qs ∈ Controls D) :
    (fun ε => payoff f Qs i - concatPayoff f ε Q Qs i -
        ((Gamma f Qs i (Qs i) - Gamma f Qs i (Q i)) * ε +
          (1 / 2) * (Lambda f ft Qs i Qs - Lambda f ft Qs i Q) * ε ^ 2))
      =o[𝓝[>] (0:ℝ)] (fun ε => ε ^ 2) := by sorry

end StrongWeakEq.Existence
