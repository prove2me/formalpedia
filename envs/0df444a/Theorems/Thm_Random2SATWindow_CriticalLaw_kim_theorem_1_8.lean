-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_kim_theorem_1_8
-- name    : Random2SATWindow.CriticalLaw.kim_theorem_1_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:37.41838+00:00
-- url     : https://prove2.me/theorems/4c0abf6f-7d0a-4fa0-8b39-e7a0003f89f9
-- title:
--   Kim's Theorem 1.8 [50], as quoted — supercritical bound $P(\mathrm{SAT})\le e^{-c_K\sigma^3n}$
-- statement:
--   There is a constant $c_K>0$ such that, whenever $\lambda=p(2n-1)=1+\sigma$, $\sigma\to0+$ and $\sigma^3n\to\infty$, the satisfiability probability of $F(n,p)$ is at most $e^{-c_K\sigma^3n}$ for all sufficiently large $n$ along the sequence. (External result of Kim [50], used in §5.1.13 for $f(x)\to0$.)
--
--   Differences from the source:
--   - reading: 'whenever λ = p(2n − 1) = 1 + σ, σ → 0+ and σ³n → ∞ … for all sufficiently large n along the sequence' → ∀ sequences (n_j, σ_j) with σ_j → 0+ (𝓝[>] 0) and σ_j³ n_j → ∞: eventually satProbBinom n_j ((1+σ_j)/(2n_j − 1)) ≤ exp(−cK σ_j³ n_j); reason: the quoted asymptotic statement made explicit over all sequences, with one c_K for all of them (BRIEF pitfall); n_j → ∞ follows from the two hypotheses
--   - encoding: 2-SAT formulas: sets of distinct legal clauses on two distinct variables; F(n, p) independent clauses, F(n, m) uniform m-subsets of the N_n = 2n(n−1) legal clauses → LegalClause n = unordered pairs (Sym2) of literals Fin n × Bool whose variables differ, Formula n = Finset (LegalClause n); probBinom n p E = Σ_{F ∈ E} p^{|F|}(1−p)^{N_n−|F|}, satProbUniform n m = #{F : |F| = m, F ∈ SAT}/C(N_n, m); reason: the paper's model verbatim; N_n = Fintype.card (LegalClause n) = 2n(n−1)
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), §5.1.13, Kim's Theorem 1.8 [50] as quoted, printed p. 58 (PDF 60)

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

/-- **Kim's Theorem 1.8 [50]**, as quoted in §5.1.13 (printed p. 58 / PDF 60). There is
`c_K > 0` such that whenever `λ = p(2n - 1) = 1 + σ` with `σ → 0+` and `σ³ n → ∞` (along any
sequence `(n_j, σ_j)` with `n_j → ∞`), `P(F(n, p) ∈ SAT) ≤ e^{-c_K σ³ n}` for all sufficiently
large `n` along the sequence (`n_j → ∞` follows from `σ_j → 0` and `σ_j³ n_j → ∞`). -/
theorem kim_theorem_1_8 :
    ∃ cK : ℝ, 0 < cK ∧ ∀ (ns : ℕ → ℕ) (σ : ℕ → ℝ),
      Tendsto σ atTop (𝓝[>] 0) →
      Tendsto (fun j => σ j ^ 3 * (ns j : ℝ)) atTop atTop →
      ∀ᶠ j in atTop, satProbBinom (ns j) ((1 + σ j) / (2 * (ns j : ℝ) - 1)) ≤
        Real.exp (-cK * σ j ^ 3 * (ns j : ℝ)) := by sorry

end Random2SATWindow.CriticalLaw
