-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_theorem_5_1_ii
-- name    : Random2SATWindow.CriticalLaw.theorem_5_1_ii
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:25.672558+00:00
-- url     : https://prove2.me/theorems/9938ca0a-c5cd-4cd8-8cc2-ea7ce9eb10f3
-- title:
--   Theorem 5.1 (ii) — exponential-moment domination and weighted $\ell^1$ convergence of the strata; $f=\sum_q\pi_q$ with geometric truncation error; conditional moments of $R$
-- statement:
--   For every $A<\infty$ there are $C_A<\infty$ and $\rho_A>1$ such that
--   $$\sup_{|x|\le A}\sum_{q\ge0}\rho_A^q\pi_q(x)\le C_A,\qquad\sup_{|x|\le A}\sum_{q\ge0}\eta^q|p_{n,q}(x)-\pi_q(x)|\longrightarrow0\quad(1\le\eta<\rho_A).\qquad(42)$$
--   Consequently $f(x)=\sum_{q\ge0}\pi_q(x)$ and $0\le f(x)-\sum_{q=0}^L\pi_q(x)\le C_A\rho_A^{-(L+1)}$ for $|x|\le A$ (43). Every fixed moment of $R(F(n,p_n(x)))$ conditional on satisfiability converges, locally uniformly in $x$, to that of $(\pi_q(x)/f(x))_{q\ge0}$.
--
--   In Lean, $f$ is the series `fProfile` together with the facts that the series has sum $f(x)$ and that $P(F(n,p_n(x))\in\mathrm{SAT})\to f(x)$.
--
--   Differences from the source:
--   - encoding: sup_{|x|≤A} Σ_q ρ_A^q π_q(x) ≤ C_A and sup_{|x|≤A} Σ_q η^q |p_{n,q} − π_q| → 0 → ∀ |x| ≤ A: Summable ∧ tsum ≤ CA; ∀ ε > 0, ∀ᶠ n, ∀ |x| ≤ A: Summable ∧ tsum ≤ ε; reason: definition of the supremum and of its convergence to 0, with summability stated so that no tsum junk value enters
--   - encoding: f(x) = Σ_q π_q(x), f the limit of the satisfiability probabilities → HasSum (π_q(x))_q (fProfile x) ∧ satProbBinom n (p_n(x)) → fProfile x; reason: f is not defined as a limit in Lean; both identifications are stated
--   - encoding: every fixed moment of R conditional on SAT, limit 'that of (π_q(x)/f(x))' → ∀ r : ℕ, condMomentR n r → (Σ' q, q^r π_q(x)) / fProfile x locally uniformly, with Σ q^r π_q(x) summable; reason: the r-th moment of the law (π_q/f)_q is Σ q^r π_q / f; ordinary moments of every order
--   - encoding: π_q(x) given by the integral (126) → piQC q x : ℂ is (126) verbatim; piQ q x = Re piQC q x, fProfile x = Σ' q, piQ q x; reason: (126) is a complex integral; Theorem 5.1(i) (theorem_5_1_i) states it is real
--   - encoding: R(F) = ½ Σ_{C ∈ SCC(D(F))} r(C) for F ∈ SAT (6) → physExcess F = (Σ_C r(C)) / 2 in ℕ, used only together with Satisfiable F; reason: on SAT the SCCs come in mirror pairs of equal excess, so the sum is even and the halving is exact
--   - encoding: 2-SAT formulas: sets of distinct legal clauses on two distinct variables; F(n, p) independent clauses, F(n, m) uniform m-subsets of the N_n = 2n(n−1) legal clauses → LegalClause n = unordered pairs (Sym2) of literals Fin n × Bool whose variables differ, Formula n = Finset (LegalClause n); probBinom n p E = Σ_{F ∈ E} p^{|F|}(1−p)^{N_n−|F|}, satProbUniform n m = #{F : |F| = m, F ∈ SAT}/C(N_n, m); reason: the paper's model verbatim; N_n = Fintype.card (LegalClause n) = 2n(n−1)
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Theorem 5.1 (ii), printed p. 21 (PDF 23); proof §5.1.9–5.1.10, printed pp. 49–53 (PDF 51–55), and §5.1.14, printed p. 59 (PDF 61)

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

/-- **Theorem 5.1 (ii)** (printed p. 21 / PDF 23; proof §5.1.9–5.1.10, printed pp. 49–53 /
PDF 51–55, and §5.1.14). For every `A < ∞` there are `C_A < ∞` and `ρ_A > 1` with
`sup_{|x| ≤ A} Σ_q ρ_A^q π_q(x) ≤ C_A` and `sup_{|x| ≤ A} Σ_q η^q |p_{n,q}(x) - π_q(x)| → 0`
for `1 ≤ η < ρ_A` (42); consequently `f(x) = Σ_q π_q(x)` (the limit of `P(F(n, p_n(x)) ∈ SAT)`)
and `0 ≤ f(x) - Σ_{q ≤ L} π_q(x) ≤ C_A ρ_A^{-(L+1)}` for `|x| ≤ A` (43). Every fixed moment of
`R(F(n, p_n(x)))` conditional on satisfiability converges, locally uniformly in `x`, to that of
`(π_q(x)/f(x))_{q ≥ 0}`. -/
theorem theorem_5_1_ii :
    (∀ A : ℝ, ∃ CA ρA : ℝ, 1 < ρA ∧
      (∀ x : ℝ, |x| ≤ A →
        Summable (fun q : ℕ => ρA ^ q * piQ q x) ∧ ∑' q : ℕ, ρA ^ q * piQ q x ≤ CA) ∧
      (∀ η : ℝ, 1 ≤ η → η < ρA → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, |x| ≤ A →
        Summable (fun q : ℕ => η ^ q * |stratumProb n q x - piQ q x|) ∧
        ∑' q : ℕ, η ^ q * |stratumProb n q x - piQ q x| ≤ ε) ∧
      (∀ x : ℝ, |x| ≤ A → ∀ L : ℕ,
        0 ≤ fProfile x - ∑ q ∈ Finset.range (L + 1), piQ q x ∧
        fProfile x - ∑ q ∈ Finset.range (L + 1), piQ q x ≤ CA * (ρA ^ (L + 1))⁻¹)) ∧
    (∀ x : ℝ, HasSum (fun q : ℕ => piQ q x) (fProfile x) ∧
      Tendsto (fun n : ℕ => satProbBinom n (critP n x)) atTop (𝓝 (fProfile x))) ∧
    (∀ (r : ℕ) (x : ℝ), Summable (fun q : ℕ => (q : ℝ) ^ r * piQ q x)) ∧
    (∀ r : ℕ, TendstoLocallyUniformly (fun (n : ℕ) (x : ℝ) => condMomentR n r x)
      (fun x => (∑' q : ℕ, (q : ℝ) ^ r * piQ q x) / fProfile x) atTop) := by sorry

end Random2SATWindow.CriticalLaw
