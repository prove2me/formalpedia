-- Prove2me | Theorems.Thm_SemisimpleQFT_theorem_4_26
-- name    : SemisimpleQFT.theorem_4_26
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:14:18.463223+00:00
-- url     : https://prove2.me/theorems/085b62f1-e4b0-45e4-b877-180e8a64b4e5
-- title:
--   Theorem 4.26: $\widetilde{\mathrm{FT}}_A|D\rangle$ is concentrated on the propagating number
-- statement:
--   There are absolute constants $C,k$ such that the following holds. Let $A\in\{P_n(d),P_{n-1/2}(d),B_n(d),B_{r,s}(d)\}$ be $\delta$-nice with $\delta\le1/2$, with a Fourier basis whose irreps carry a size function $|\cdot|$ satisfying the conclusions of Theorem 4.17 ($\lambda(D)=0$ whenever $\mathrm{pn}(D)<|\lambda|$) and Theorem 4.16 ($|\{D\in\mathcal D(A):\mathrm{pn}(D)=r\}|=\sum_{|\rho|=r}d_\rho^2$ for all $r$). Let $a=d^{(n-\mathrm{cc}(D))/2}D\in\mathcal B(A)$, $|\tilde a\rangle=\widetilde{\mathrm{FT}}_A|a\rangle$, and let $\Pi_r$ be the projection onto the span of the states $|\lambda,i,j\rangle$ with $|\lambda|=r$. If $D$ has propagating number $r$, then
--   $$\big|\langle\tilde a|\Pi_r|\tilde a\rangle_0-\langle\tilde a,\tilde a\rangle_0\big|\le C\,|A|^k\,\delta .$$
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 30, Theorem 4.26, Eqs. (4.23)–(4.24); proof in Appendix C, p. 57

import Definitions.Def_SemisimpleQFT_Diagram

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem theorem_4_26 :
    ∃ (C : ℝ) (k : ℕ), ∀ (n d : ℕ) (S : Set (Diagram n)) (Λ J : Type) [Fintype J] [DecidableEq J]
      (F : FourierData (diagramAlgebra S d) Λ J) (size : Λ → ℕ) (δ : ℝ),
      IsStdFamily n d S → IsVanishing F size →
      (∀ r : ℕ, Nat.card {D : S // pn D.1 = r} =
        Nat.card {p : F.Idx // size (F.lab p.row) = r}) →
      δ ≤ 1 / 2 → F.IsNice (diagBasis S d) δ →
      ∀ D : S, concentrationDefect F size D ≤ C * (Nat.card S : ℝ) ^ k * δ := by sorry

end SemisimpleQFT
