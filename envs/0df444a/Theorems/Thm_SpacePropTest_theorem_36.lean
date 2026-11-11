-- Prove2me | Theorems.Thm_SpacePropTest_theorem_36
-- name    : SpacePropTest.theorem_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:09.118387+00:00
-- url     : https://prove2.me/theorems/a76caf84-242b-48e6-bce0-8f54d502f4fb
-- title:
--   Theorem 36, p.32 — a corrupting $(I,\beta)$-block system rules out $(\beta/10,1/3)$-testers in normal form with $M^3\sqrt{\log M}<\beta\sqrt{|I|}/400$
-- statement:
--   Let $\mathcal P$ be a property of Boolean functions on $\{0,1\}^n$ and suppose an $(I,\beta)$-block system corrupts $\mathcal P$. If $A$ is an $M$-state tester in normal form and
--
--   $$M^3\sqrt{\log M}<\frac{\beta}{400}\sqrt{|I|},$$
--
--   then $A$ is not a $(\beta/10,1/3)$-tester for $\mathcal P$.
--
--   Both the symmetry lower bound (Theorem 38) and the monotonicity lower bound (Theorem 41) are instances.
--
--   Differences from the source:
--   - encoding: states $[M]$ with state 1 initial → a finite type $\sigma$ with a designated start state, $M=|\sigma|$; reason: any finite type is in bijection with $[M]$
--   - reading: $\log(M)$ → the natural logarithm $\ln M$; reason: the proof (p.32) uses $\Lambda=4\sqrt{|I|\log M}$ in a Hoeffding bound $2e^{-\Lambda^2/(2|I|)}$, which is natural-log; $\ln\le\log_2$, so this hypothesis is the weaker one and the theorem the stronger
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Theorem 36, p.32 (PDF 34); Definitions 34–35, p.31 (PDF 33)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain
import Definitions.Def_SpacePropTest_Tester
import Definitions.Def_SpacePropTest_BlockSystem

set_option autoImplicit false

namespace SpacePropTest

/-- **Theorem 36** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.32 (PDF 34)).
Let `P` be a property of Boolean functions such that there exists an `(I, β)`-block system that
corrupts `P`. If `A` is an `M`-state tester in normal form, and `M³ √(log M) < (β/400) √|I|`, then
`A` is not a `(β/10, 1/3)`-tester for `P`.

**Formalization Note.** `M = |σ|`, `log` is the natural logarithm (paper.md decision 11). -/
theorem theorem_36 {n : ℕ} (P : Set (BoolFn n)) {I : Type*} [Fintype I] [DecidableEq I]
    {β : ℝ} (S : BlockSystem n I β) (hS : S.Corrupts P)
    {σ : Type*} [Fintype σ] [DecidableEq σ] (A : Tester n σ) (hA : A.IsNormalForm)
    (hM : (Fintype.card σ : ℝ) ^ 3 * Real.sqrt (Real.log (Fintype.card σ)) <
      β / 400 * Real.sqrt (Fintype.card I)) :
    ¬ A.IsTester P (β / 10) (1 / 3) := by sorry

end SpacePropTest
