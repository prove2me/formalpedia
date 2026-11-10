-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_theorem_5_1_iii
-- name    : Random2SATWindow.CriticalLaw.theorem_5_1_iii
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:45.701224+00:00
-- url     : https://prove2.me/theorems/3a949103-95f6-4899-be00-54aa6661051c
-- title:
--   Theorem 5.1 (iii) — scalar profile: $f$ nonincreasing into $(0,1)$, locally uniform limit in both models, left tail (44) and right tail (45)
-- statement:
--   The function $f$ is nonincreasing, takes values in $(0,1)$, and is the locally uniform limit of the satisfiability probabilities in both the independent-clause model $F(n,p_n(x))$ and the fixed-size model $F(n,\lfloor n+xn^{2/3}\rfloor)$. Moreover
--   $$1-f(-t)=\frac1{16t^3}-\frac{113}{512t^6}+O(t^{-9})\quad(t\to+\infty),\qquad(44)$$
--   $$f(x)\longrightarrow0,\qquad c_0x^3\le-\log f(x)\le\frac{x^3}6+O(x)\quad(x\to+\infty),\qquad c_0>0.\qquad(45)$$
--
--   Differences from the source:
--   - encoding: O(t^{−9}) as t → +∞ in (44); 'c_0 x³ ≤ −log f(x) ≤ x³/6 + O(x) (x → +∞)' in (45) → ∃ C T0, ∀ t ≥ T0, |1 − f(−t) − (1/(16t³) − 113/(512t⁶))| ≤ C/t⁹; ∃ c0 > 0, ∃ C X0, ∀ x ≥ X0, c0 x³ ≤ −log f(x) ∧ −log f(x) ≤ x³/6 + C x; reason: explicit forms of O(·): two-sided for the expansion (44), one-sided as printed in (45)
--   - encoding: m = ⌊n + x n^{2/3}⌋ → critM n x = Int.toNat ⌊n + x n^{2/3}⌋; reason: negative only for finitely many n on each compact x-set, so the locally uniform limit is unchanged
--   - encoding: f → fProfile = Σ' q, Re π_q (the series of Theorem 3.1); reason: f is not defined as a limit; the limit statements are clauses
--   - encoding: 2-SAT formulas: sets of distinct legal clauses on two distinct variables; F(n, p) independent clauses, F(n, m) uniform m-subsets of the N_n = 2n(n−1) legal clauses → LegalClause n = unordered pairs (Sym2) of literals Fin n × Bool whose variables differ, Formula n = Finset (LegalClause n); probBinom n p E = Σ_{F ∈ E} p^{|F|}(1−p)^{N_n−|F|}, satProbUniform n m = #{F : |F| = m, F ∈ SAT}/C(N_n, m); reason: the paper's model verbatim; N_n = Fintype.card (LegalClause n) = 2n(n−1)
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Theorem 5.1 (iii), printed p. 21 (PDF 23); proof §5.1.11–5.1.13, printed pp. 54–58 (PDF 56–60), and §5.1.14, printed p. 59 (PDF 61)

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

/-- **Theorem 5.1 (iii)** (printed p. 21 / PDF 23; proof §5.1.11–5.1.13, printed pp. 54–58 /
PDF 56–60, and §5.1.14). `f` is nonincreasing, takes values in `(0, 1)`, and is the locally
uniform limit of the satisfiability probabilities in both the independent-clause and the
fixed-size models. Moreover `1 - f(-t) = 1/(16t³) - 113/(512t⁶) + O(t^{-9})` as `t → +∞` (44),
and `f(x) → 0`, `c_0 x³ ≤ -log f(x) ≤ x³/6 + O(x)` as `x → +∞`, with `c_0 > 0` (45). -/
theorem theorem_5_1_iii :
    Antitone fProfile ∧ (∀ x : ℝ, 0 < fProfile x ∧ fProfile x < 1) ∧
    TendstoLocallyUniformly (fun (n : ℕ) (x : ℝ) => satProbBinom n (critP n x)) fProfile atTop ∧
    TendstoLocallyUniformly (fun (n : ℕ) (x : ℝ) => satProbUniform n (critM n x)) fProfile
      atTop ∧
    (∃ C T0 : ℝ, ∀ t : ℝ, T0 ≤ t →
      |1 - fProfile (-t) - (1 / (16 * t ^ 3) - 113 / (512 * t ^ 6))| ≤ C / t ^ 9) ∧
    Tendsto fProfile atTop (𝓝 0) ∧
    (∃ c0 : ℝ, 0 < c0 ∧ ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      c0 * x ^ 3 ≤ -Real.log (fProfile x) ∧ -Real.log (fProfile x) ≤ x ^ 3 / 6 + C * x) := by sorry

end Random2SATWindow.CriticalLaw
