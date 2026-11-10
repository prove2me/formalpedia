-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_theorem_5_1_i
-- name    : Random2SATWindow.CriticalLaw.theorem_5_1_i
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:28.457193+00:00
-- url     : https://prove2.me/theorems/e0041685-90da-459b-a9cc-42c387c7b06e
-- title:
--   Theorem 5.1 (i) — every fixed-excess stratum converges: $p_{n,q}\to\pi_q$ locally uniformly, $\pi_q$ the absolutely convergent Airy integral (126)
-- statement:
--   There are continuous functions $\pi_q:\mathbb R\to[0,1]$, $q\ge0$, such that for each fixed $q$, $p_{n,q}\to\pi_q$ locally uniformly. Each $\pi_q$ is a finite sum of absolutely convergent integrals of products of generalized Airy functions divided by powers of $A_1$; the coefficients and integrals are specified in (84)–(126). In particular $\pi_0(x)=2^{-1/6}Q_{1/2;0}(x;\emptyset)$.
--
--   In Lean, for each $q$: $\pi_q$ of (126) is continuous, real valued with $0\le\pi_q\le1$; $p_{n,q}\to\pi_q$ locally uniformly; the integrand of (126) and the integrand of each Airy monomial $(-1)^kN_{j_0}D_{j_1}\cdots D_{j_k}/D_0^{k+1}$ of $R_q$ are integrable, and $\pi_q(x)$ is the finite sum of the monomial integrals; and $\pi_0(x)=2^{-1/6}Q_{1/2;0}(x;\emptyset)$ with $Q$ from (34).
--
--   Differences from the source:
--   - encoding: π_q(x) given by the integral (126) → piQC q x : ℂ is (126) verbatim; piQ q x = Re piQC q x, fProfile x = Σ' q, piQ q x; reason: (126) is a complex integral; Theorem 5.1(i) (theorem_5_1_i) states it is real
--   - encoding: 'a finite sum of absolutely convergent integrals of products of generalized Airy functions divided by powers of A_1' → π_q(x) = Σ_{j0 ≤ q} Σ_{c : Composition (q − j0)} piPrefactor x · ∫ piTermIntegrand q j0 c x, each piTermIntegrand Integrable (and piIntegrand Integrable); reason: the monomials are the unfolding of the recursion (121) (cf. (54)); Integrable is absolute convergence
--   - encoding: p_{n,q} → π_q locally uniformly (real functions) → TendstoLocallyUniformly of the casts (p_{n,q}(x) : ℂ) to piQC q; reason: π_q is defined as a complex integral; equivalent since π_q is real
--   - encoding: Π with any fixed c > 0 in (30), (32) → contourPi with c = 1 (rays 1 + t e^{±iπ/3}, t > 0); reason: the paper notes the value does not depend on c > 0
--   - encoding: R(F) = ½ Σ_{C ∈ SCC(D(F))} r(C) for F ∈ SAT (6) → physExcess F = (Σ_C r(C)) / 2 in ℕ, used only together with Satisfiable F; reason: on SAT the SCCs come in mirror pairs of equal excess, so the sum is even and the halving is exact
--   - encoding: 2-SAT formulas: sets of distinct legal clauses on two distinct variables; F(n, p) independent clauses, F(n, m) uniform m-subsets of the N_n = 2n(n−1) legal clauses → LegalClause n = unordered pairs (Sym2) of literals Fin n × Bool whose variables differ, Formula n = Finset (LegalClause n); probBinom n p E = Σ_{F ∈ E} p^{|F|}(1−p)^{N_n−|F|}, satProbUniform n m = #{F : |F| = m, F ∈ SAT}/C(N_n, m); reason: the paper's model verbatim; N_n = Fintype.card (LegalClause n) = 2n(n−1)
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Theorem 5.1 (i), printed p. 21 (PDF 23); proof §5.1.4–5.1.8, printed pp. 39–49 (PDF 41–51), and §5.1.14, printed p. 59 (PDF 61)

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

/-- **Theorem 5.1 (i)** (refined critical satisfiability law, printed p. 21 / PDF 23; proof
§5.1.4–5.1.8, printed pp. 39–49 / PDF 41–51, and §5.1.14). For each fixed `q`, `π_q` given by
(126) is a continuous function `ℝ → [0, 1]` (real valued), `p_{n,q} → π_q` locally uniformly,
and `π_q` is a finite sum of absolutely convergent integrals of products of generalized Airy
functions divided by powers of `A_1` (the monomials of `R_q`, cf. (54)); in particular
`π_0(x) = 2^{-1/6} Q_{1/2;0}(x; ∅)`. -/
theorem theorem_5_1_i (q : ℕ) :
    Continuous (piQC q) ∧
    (∀ x, (piQC q x).im = 0 ∧ 0 ≤ (piQC q x).re ∧ (piQC q x).re ≤ 1) ∧
    TendstoLocallyUniformly (fun (n : ℕ) (x : ℝ) => ((stratumProb n q x : ℝ) : ℂ)) (piQC q)
      atTop ∧
    (∀ x, Integrable (piIntegrand q x) ∧
      (∀ (j0 : Fin (q + 1)) (c : Composition (q - j0)), Integrable (piTermIntegrand q j0 c x)) ∧
      piQC q x = ∑ j0 : Fin (q + 1), ∑ c : Composition (q - j0),
        (piPrefactor x : ℂ) * ∫ θ : ℝ, piTermIntegrand q j0 c x θ) ∧
    (∀ x, piQC 0 x = (((2 : ℝ) ^ (-(1 / 6 : ℝ)) : ℝ) : ℂ) * quotientQ (1 / 2) 0 ![] x) := by sorry

end Random2SATWindow.CriticalLaw
