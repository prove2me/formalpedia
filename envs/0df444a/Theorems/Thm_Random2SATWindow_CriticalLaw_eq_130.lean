-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_eq_130
-- name    : Random2SATWindow.CriticalLaw.eq_130
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:20.425786+00:00
-- url     : https://prove2.me/theorems/f22e17a0-9b94-44f2-af94-e0a4c664a574
-- title:
--   (130) — Kim's pure-literal-core concentration in the slightly supercritical range, as the paper reads it
-- statement:
--   For $\lambda=1+\sigma>1$ let $\vartheta$ be the positive solution of $\vartheta=1-e^{-\lambda\vartheta}$. There are constants $\sigma_*,L_*,C_*,c_*>0$ such that
--   $$P\big(b_C>C_*\vartheta^2n\ \text{or}\ m_K>C_*\vartheta^3n\big)\le C_*e^{-c_*\vartheta^3n}\qquad(130)$$
--   for all sufficiently large $n$, uniformly when $p=\frac{1+\sigma}{2n-1}$, $0<\sigma\le\sigma_*$, $\sigma n^{1/3}\ge L_*$. (The paper derives this from Kim [50, Theorem 3.3, Main Lemma 3.1] under its stated reading of Kim's constants.)
--
--   Differences from the source:
--   - reading: 'for all sufficiently large n, uniformly when p = (1+σ)/(2n−1), 0 < σ ≤ σ∗, σn^{1/3} ≥ L∗' → ∃ N, ∀ n ≥ N, ∀ σ ∈ (0, σs] with Ls ≤ σ n^{1/3}: the bound; reason: 'uniformly' read as one threshold N for all admissible σ, the stronger reading and the one Lemma 5.7 uses
--   - encoding: ϑ, the positive solution of ϑ = 1 − e^{−λϑ} → ∀ ϑ > 0 with ϑ = 1 − exp(−(1+σ)ϑ); reason: for λ > 1 the positive solution exists and is unique, so quantifying over it is the same
--   - encoding: m_K, the clause count of the reduced kernel (suppression of (1,1) core variables, discarding zero-excess cycle components) → kernelClauses F = m_C − #{core variables of degree 2}; reason: the closed form of the paper's count: each suppression removes one variable and one clause and preserves other degrees; discarded cycles have as many clauses as variables
--   - encoding: 2-SAT formulas: sets of distinct legal clauses on two distinct variables; F(n, p) independent clauses, F(n, m) uniform m-subsets of the N_n = 2n(n−1) legal clauses → LegalClause n = unordered pairs (Sym2) of literals Fin n × Bool whose variables differ, Formula n = Finset (LegalClause n); probBinom n p E = Σ_{F ∈ E} p^{|F|}(1−p)^{N_n−|F|}, satProbUniform n m = #{F : |F| = m, F ∈ SAT}/C(N_n, m); reason: the paper's model verbatim; N_n = Fintype.card (LegalClause n) = 2n(n−1)
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), §5.1.9, equation (130), printed p. 51 (PDF 53); deduction printed pp. 51–52 (PDF 53–54)

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

/-- **(130)** (§5.1.9, printed p. 51 / PDF 53; Kim [50, Theorem 3.3 and Main Lemma 3.1] in the
paper's reading). There are `σ_*, L_*, C_*, c_* > 0` such that for all sufficiently large `n`,
uniformly in `σ` with `0 < σ ≤ σ_*` and `σ n^{1/3} ≥ L_*`, with `p = (1+σ)/(2n-1)`,
`λ = 1 + σ` and `ϑ` the positive solution of `ϑ = 1 - e^{-λϑ}`:
`P(b_C > C_* ϑ² n or m_K > C_* ϑ³ n) ≤ C_* e^{-c_* ϑ³ n}`. -/
theorem eq_130 :
    ∃ σs Ls Cs cs : ℝ, 0 < σs ∧ 0 < Ls ∧ 0 < Cs ∧ 0 < cs ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ σ : ℝ, 0 < σ → σ ≤ σs → Ls ≤ σ * (n : ℝ) ^ (1 / 3 : ℝ) →
        ∀ ϑ : ℝ, 0 < ϑ → ϑ = 1 - Real.exp (-(1 + σ) * ϑ) →
          probBinom n ((1 + σ) / (2 * (n : ℝ) - 1))
              (fun F => Cs * ϑ ^ 2 * n < (coreVars F : ℝ) ∨ Cs * ϑ ^ 3 * n < (kernelClauses F : ℝ))
            ≤ Cs * Real.exp (-cs * ϑ ^ 3 * n) := by sorry

end Random2SATWindow.CriticalLaw
