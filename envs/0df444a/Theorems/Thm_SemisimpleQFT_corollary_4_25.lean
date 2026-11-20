-- Prove2me | Theorems.Thm_SemisimpleQFT_corollary_4_25
-- name    : SemisimpleQFT.corollary_4_25
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:13:40.277412+00:00
-- url     : https://prove2.me/theorems/94835b1a-9a7d-4794-a027-e24f3045c688
-- title:
--   Corollary 4.25: the diagram algebras are $O(d^{-1/2}|A|)$-nice
-- statement:
--   There is an absolute constant $C$ such that for any $A\in\{P_n(d),P_{n-1/2}(d),B_n(d),B_{r,s}(d)\}$ with its scaled diagram basis $\mathcal B(A)$ (Eq. (4.10)) and any Fourier basis of $A$ in the orthogonal form, if $d^{-1/2}|A|\le1/2$ then $A$ is $\delta$-nice with
--   $$\delta=C\,d^{-1/2}|A| .$$
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 29, Corollary 4.25

import Definitions.Def_SemisimpleQFT_Diagram

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem corollary_4_25 :
    ∃ C : ℝ, ∀ (n d : ℕ) (S : Set (Diagram n)) (Λ J : Type) [Fintype J] [DecidableEq J]
      (F : FourierData (diagramAlgebra S d) Λ J),
      IsStdFamily n d S → IsOrthogonalForm F →
      (Nat.card S : ℝ) / Real.sqrt (d : ℝ) ≤ 1 / 2 →
      F.IsNice (diagBasis S d) (C * (Nat.card S : ℝ) / Real.sqrt (d : ℝ)) := by sorry

end SemisimpleQFT
