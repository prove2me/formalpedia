-- Prove2me | Theorems.Thm_SemisimpleQFT_theorem_4_16
-- name    : SemisimpleQFT.theorem_4_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:58:27.097673+00:00
-- url     : https://prove2.me/theorems/145fedaf-b875-4762-8883-94f34a2d1446
-- title:
--   Theorem 4.16: $|\{D\in\mathcal D(A):\mathrm{pn}(D)=k\}|=\sum_{|\rho|=k}d_\rho^2$
-- statement:
--   For $A\in\{B_n(d),B_{r,s}(d),P_n(d)\}$ and every $k$,
--   $$\big|\{D\in\mathcal D(A):\mathrm{pn}(D)=k\}\big|=\sum_{\rho\in\widehat A:\ |\rho|=k}d_\rho^2 .$$
--   Here $\widehat A$ is the set of Young-diagram labels of Theorems 4.12, 4.14, 4.15 and $d_\rho$ is the dimension of the irrep $\rho$, which is the number of Bratteli paths from the root to $\rho$ in the Bratteli diagram of the chain of Section 5.3 (branching rules of Theorem 5.2). The formal statement counts, on the right, the pairs of Bratteli paths with a common endpoint of size $k$; for $B_{r,s}(d)$ it is stated for $r\le s$ and $|(\lambda,\mu)|=|\lambda|+|\mu|$.
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 26, Theorem 4.16, Eq. (4.11); proof in Appendix B, p. 54

import Definitions.Def_SemisimpleQFT_Chains

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem theorem_4_16 :
    (∀ n k : ℕ,
      Nat.card {D : Diagram n // IsBrauer D ∧ pn D = k} =
        Nat.card {pq : (brauerBratteli n).Path n × (brauerBratteli n).Path n //
          pq.1.last = pq.2.last ∧ pq.1.last.size = k}) ∧
    (∀ r s k : ℕ, r ≤ s →
      Nat.card {D : Diagram (r + s) // IsWalled r D ∧ pn D = k} =
        Nat.card {pq : (walledBratteli r (r + s)).Path (r + s) ×
            (walledBratteli r (r + s)).Path (r + s) //
          pq.1.last = pq.2.last ∧ pairSize pq.1.last = k}) ∧
    (∀ n k : ℕ,
      Nat.card {D : Diagram n // pn D = k} =
        Nat.card {pq : (partitionBratteli n).Path (2 * n) × (partitionBratteli n).Path (2 * n) //
          pq.1.last = pq.2.last ∧ pq.1.last.size = k}) := by sorry

end SemisimpleQFT
