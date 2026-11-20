-- Prove2me | Theorems.Thm_SemisimpleQFT_theorem_6_12
-- name    : SemisimpleQFT.theorem_6_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:59:53.929209+00:00
-- url     : https://prove2.me/theorems/d4dfbc02-2a71-40ef-8e24-f56f301b8e2d
-- title:
--   Theorem 6.12: an efficient quantum Fourier transform for $B_n(d)$, $B_{r,s}(d)$ and $P_n(d)$
-- statement:
--   Let $A\in\{B_n(d),B_{r,s}(d),P_n(d)\}$ (with $n=r+s$ for the walled Brauer algebra). The Fourier transform $\mathrm{FT}_A$ can be implemented on a quantum computer up to operator norm error
--   $$O\big(\mathrm{poly}(|A|)\cdot d^{-1/2}+\varepsilon\big)$$
--   by quantum circuits with gate complexity
--   $$\widetilde O\big(n^{15/2}\cdot(\sqrt n+\log d+\log(1/\varepsilon))\big)\ \text{ for }B_n(d)\text{ and }B_{r,s}(d),\qquad \widetilde O\big(n^{15/2}\cdot(n+\log d+\log(1/\varepsilon))\big)\ \text{ for }P_n(d).$$
--   The Fourier transform is performed with respect to the subalgebra adapted bases from Section 5.3 and the orthogonal form in Section 5.4.
--
--   **Precise form.** There are absolute constants $C$ and $k$ such that for every $n$ (resp. $r\le s$), every $d$ in the semisimple range ($d\notin\{0,\dots,n\}$ for $B_n(d)$, $d\notin\{0,\dots,r+s-2\}$ for $B_{r,s}(d)$, $d\notin\{0,\dots,2n-2\}$ for $P_n(d)$) and every $0<\varepsilon\le1$, there exist a subalgebra adapted system of Fourier bases for the chain of Section 5.3 that is in the orthogonal form and labelled as in Theorem 4.17, and a circuit of one- and two-qubit unitary gates with at most $C\,f\,\log(2+f)^k$ gates, $f$ being the expression inside $\widetilde O$, such that
--   $$\big\|U\,J_{\mathrm{in}}-J_{\mathrm{out}}\,\mathrm{FT}_A\big\|_\infty\le C\big(|A|^k\,d^{-1/2}+\varepsilon\big).$$
--   Here $\mathrm{FT}_A$ is the normalized Fourier transform of Definition 3.1 from the scaled diagram basis $\mathcal B(A)$ (Eq. (4.10)) to the states $|\rho,P,Q\rangle$; $J_{\mathrm{in}}$ stores a basis element by the bit string of its diagram and $J_{\mathrm{out}}$ stores $|\rho,P,Q\rangle$ by the bit strings of the Bratteli paths $P$ and $Q$, all remaining qubits being $|0\rangle$ before and after.
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 52, Theorem 6.12, Eqs. (6.82)–(6.84)

import Definitions.Def_SemisimpleQFT_Circuit

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem theorem_6_12 :
    ∃ (C : ℝ) (k : ℕ),
      (∀ (n d : ℕ) (ε : ℝ), n < d → 0 < ε → ε ≤ 1 →
        HasEfficientQFT n (brauerLevel n) d (brauerBratteli n) Shape.size shapeBits
          (softO C k ((n : ℝ) ^ ((15 : ℝ) / 2) *
            (Real.sqrt (n : ℝ) + Real.log (d : ℝ) + Real.log (1 / ε))))
          (C * ((Nat.card (brauerLevel n n) : ℝ) ^ k / Real.sqrt (d : ℝ) + ε))) ∧
      (∀ (r s d : ℕ) (ε : ℝ), r ≤ s → r + s < d + 2 → 0 < ε → ε ≤ 1 →
        HasEfficientQFT (r + s) (walledLevel r (r + s)) d (walledBratteli r (r + s))
          pairSize pairBits
          (softO C k (((r + s : ℕ) : ℝ) ^ ((15 : ℝ) / 2) *
            (Real.sqrt ((r + s : ℕ) : ℝ) + Real.log (d : ℝ) + Real.log (1 / ε))))
          (C * ((Nat.card (walledLevel r (r + s) (r + s)) : ℝ) ^ k / Real.sqrt (d : ℝ) + ε))) ∧
      (∀ (n d : ℕ) (ε : ℝ), 2 * n < d + 2 → 0 < ε → ε ≤ 1 →
        HasEfficientQFT (2 * n) (partitionLevel n) d (partitionBratteli n) Shape.size shapeBits
          (softO C k ((n : ℝ) ^ ((15 : ℝ) / 2) *
            ((n : ℝ) + Real.log (d : ℝ) + Real.log (1 / ε))))
          (C * ((Nat.card (partitionLevel n (2 * n)) : ℝ) ^ k / Real.sqrt (d : ℝ) + ε))) := by sorry

end SemisimpleQFT
