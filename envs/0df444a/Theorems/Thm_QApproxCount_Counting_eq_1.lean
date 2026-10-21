-- Prove2me | Theorems.Thm_QApproxCount_Counting_eq_1
-- name    : QApproxCount.Counting.eq_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:22.401459+00:00
-- url     : https://prove2.me/theorems/902ab6c4-97f8-4242-8e87-24da5481e4f2
-- title:
--   Eq. (1), corrected — G^{(r−1)/2}|ψ⟩ = (−1)^{(r−1)/2}(sin(rθ)/√K Σ_{x∈S}|x⟩ + cos(rθ)/√(N−K) Σ_{x∉S}|x⟩), marked probability sin²(rθ)
-- statement:
--   Let $T\subseteq[n]$ with $0<|T|<n$, let $\theta := \arcsin\sqrt{|T|/n}$, and let $r$ be an odd natural number. With $U$, $|\psi\rangle$ and $G=(I-2|\psi\rangle\langle\psi|)U$ as in the model,
--   $$G^{(r-1)/2}|\psi\rangle = (-1)^{(r-1)/2}\left(\frac{\sin(r\theta)}{\sqrt{|T|}}\sum_{x\in T}|x\rangle + \frac{\cos(r\theta)}{\sqrt{n-|T|}}\sum_{x\notin T}|x\rangle\right),$$
--   and the probability of observing a marked item when this state is measured in the computational basis is $\sin^2(r\theta)$.
--
--   This is the statement that turns every measurement round of the algorithm into a coin with bias $\sin^2(r\theta)$.
--
--   **Formalization Note** This is a corrected version of the paper's eq. (1). The paper prints the identity without the global sign $(-1)^{(r-1)/2}$. Since $G=-(2|\psi\rangle\langle\psi|-I)U$ is minus the standard Grover iterate, each application contributes a factor $-1$. The printed identity fails for $r=3,7$ (checked numerically for $n=7$, $|T|=2$). The probability statement is unaffected.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 5, eq. (1) (corrected: global phase (−1)^{(r−1)/2})

import Mathlib
import Definitions.Def_QApproxCount_Counting_Grover

namespace QApproxCount.Counting

/-- Eq. (1), p. 5, **corrected**: for `0 < |T| < n`, odd `r` and `θ := arcsin √(|T|/n)`,
`G^{(r-1)/2}|ψ⟩ = (-1)^{(r-1)/2} ( sin(rθ)/√|T| Σ_{x∈T} |x⟩ + cos(rθ)/√(n-|T|) Σ_{x∉T} |x⟩ )`
(the paper omits the sign `(-1)^{(r-1)/2}`, which comes from `G = (I - 2|ψ⟩⟨ψ|)U`), and the
Born probability of a marked outcome is `sin²(rθ)`. -/
theorem eq_1 {n : ℕ} (T : Finset (Fin n)) (hT : 0 < T.card) (hTn : T.card < n)
    (r : ℕ) (hr : Odd r) :
    groverState T ((r - 1) / 2) =
        (fun x => (-1 : ℂ) ^ ((r - 1) / 2) *
          (if x ∈ T then
            ((Real.sin (r * Real.arcsin (Real.sqrt ((T.card : ℝ) / n))) /
              Real.sqrt (T.card : ℝ) : ℝ) : ℂ)
          else
            ((Real.cos (r * Real.arcsin (Real.sqrt ((T.card : ℝ) / n))) /
              Real.sqrt ((n : ℝ) - T.card) : ℝ) : ℂ))) ∧
      markedProb T ((r - 1) / 2) =
        Real.sin (r * Real.arcsin (Real.sqrt ((T.card : ℝ) / n))) ^ 2 := by sorry

end QApproxCount.Counting
