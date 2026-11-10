-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_lemma_5_7
-- name    : Random2SATWindow.CriticalLaw.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:34.188293+00:00
-- url     : https://prove2.me/theorems/27e9e0f7-3e7a-4db4-9a87-48db242095ea
-- title:
--   Lemma 5.7 — unconditional exponential tail of the core excess $X$, uniformly on compact critical windows
-- statement:
--   For each $A<\infty$ there are $C_A,c_A>0$ and $n_A$ such that
--   $$\sup_{n\ge n_A,\ |x|\le A}P\big(X(F(n,p_n(x)))\ge k\big)\le C_Ae^{-c_Ak}\qquad(k\ge1).\qquad(131)$$
--
--   Differences from the source:
--   - encoding: sup_{n ≥ n_A, |x| ≤ A} P(…) ≤ C_A e^{−c_A k} → ∀ n ≥ nA, ∀ x with |x| ≤ A, the bound; reason: a bound on a supremum of a bounded family is the bound for every member
--   - encoding: 2-SAT formulas: sets of distinct legal clauses on two distinct variables; F(n, p) independent clauses, F(n, m) uniform m-subsets of the N_n = 2n(n−1) legal clauses → LegalClause n = unordered pairs (Sym2) of literals Fin n × Bool whose variables differ, Formula n = Finset (LegalClause n); probBinom n p E = Σ_{F ∈ E} p^{|F|}(1−p)^{N_n−|F|}, satProbUniform n m = #{F : |F| = m, F ∈ SAT}/C(N_n, m); reason: the paper's model verbatim; N_n = Fintype.card (LegalClause n) = 2n(n−1)
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Lemma 5.7, printed p. 52 (PDF 54); proof printed pp. 52–53 (PDF 54–55)

import Mathlib
import Definitions.Def_Random2SATWindow_CriticalLaw_Formulas
import Definitions.Def_Random2SATWindow_CriticalLaw_Airy
import Definitions.Def_Random2SATWindow_CriticalLaw_Hadamard
import Definitions.Def_Random2SATWindow_CriticalLaw_Strata
import Definitions.Def_Random2SATWindow_CriticalLaw_Saddle
import Definitions.Def_Random2SATWindow_CriticalLaw_PureLiteral

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace Random2SATWindow.CriticalLaw

/-- **Lemma 5.7** (unconditional exponential tail, printed p. 52 / PDF 54). For each
`A < ∞` there are `C_A, c_A > 0` and `n_A` such that
`sup_{n ≥ n_A, |x| ≤ A} P(X(F(n, p_n(x))) ≥ k) ≤ C_A e^{-c_A k}` for every `k ≥ 1` (131). -/
theorem lemma_5_7 (A : ℝ) :
    ∃ CA cA : ℝ, 0 < CA ∧ 0 < cA ∧ ∃ nA : ℕ, ∀ n : ℕ, nA ≤ n → ∀ x : ℝ, |x| ≤ A →
      ∀ k : ℕ, 1 ≤ k →
        probBinom n (critP n x) (fun F => (k : ℤ) ≤ coreExcess F) ≤ CA * Real.exp (-cA * k) := by sorry

end Random2SATWindow.CriticalLaw
