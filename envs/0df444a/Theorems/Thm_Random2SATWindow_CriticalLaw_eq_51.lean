-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_eq_51
-- name    : Random2SATWindow.CriticalLaw.eq_51
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:14.773284+00:00
-- url     : https://prove2.me/theorems/ac0523e3-c2df-49d0-a392-4b322b2e6075
-- title:
--   (51) — the exact marked implication quotient for $H_n(x,y)=\sum_q p_{n,q}(x)y^q$
-- statement:
--   Let $p=p_n(x)\in(0,1)$, $w=p/(1-p)$, and $S(z,w;y)=S_0(z,w)+\sum_{r\ge1}y^rS_r(z,w)$ (Lemma 5.2 with $\varphi(C)=y^{r(C)}$). Then, as polynomials in $y$,
--   $$H_n(x,y):=\sum_{q\ge0}p_{n,q}(x)y^q=\frac{2^nn!}{(1+w)^{n(n-1)}}\,[z^n]\,\frac{e^{-S(2z,w;y)/2}\odot I_0(z,w)}{e^{-S(z,w;y)}\odot D_0(z,w)}.\qquad(51)$$
--   The quotient is taken in $\mathbb R[y][[z]]$; the denominator has constant term $1$, so it is invertible (`PowerSeries.invOfUnit … 1`).
--
--   Differences from the source:
--   - encoding: the quotient of two formal power series in z, with y a formal marker → numerator * PowerSeries.invOfUnit denominator 1 in (Polynomial ℝ)⟦z⟧; reason: the denominator's constant coefficient is 0!·1·1 = 1 (B_0(0, w) = 1, as the paper notes), so invOfUnit … 1 is its inverse
--   - encoding: p = p_n(x), used only when 0 < p < 1 (standing assumption of §5.1) → hypotheses 0 < critP n x and critP n x < 1; reason: w = p/(1−p) and the clause model need 0 < p < 1; the paper states this restriction at the head of §5.1
--   - encoding: R(F) = ½ Σ_{C ∈ SCC(D(F))} r(C) for F ∈ SAT (6) → physExcess F = (Σ_C r(C)) / 2 in ℕ, used only together with Satisfiable F; reason: on SAT the SCCs come in mirror pairs of equal excess, so the sum is even and the halving is exact
--   - encoding: 2-SAT formulas: sets of distinct legal clauses on two distinct variables; F(n, p) independent clauses, F(n, m) uniform m-subsets of the N_n = 2n(n−1) legal clauses → LegalClause n = unordered pairs (Sym2) of literals Fin n × Bool whose variables differ, Formula n = Finset (LegalClause n); probBinom n p E = Σ_{F ∈ E} p^{|F|}(1−p)^{N_n−|F|}, satProbUniform n m = #{F : |F| = m, F ∈ SAT}/C(N_n, m); reason: the paper's model verbatim; N_n = Fintype.card (LegalClause n) = 2n(n−1)
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), §5.1.1, equation (51), printed p. 25 (PDF 27)

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

/-- **(51)** (exact marked implication quotient, printed p. 25 / PDF 27). With
`p = p_n(x) ∈ (0, 1)` and `w = p/(1-p)`,
`H_n(x, y) = Σ_q p_{n,q}(x) y^q = (2^n n! / (1+w)^{n(n-1)}) [z^n]
  (e^{-S(2z,w;y)/2} ⊙ I_0(z,w)) / (e^{-S(z,w;y)} ⊙ D_0(z,w))`,
an identity of polynomials in `y` (the denominator has constant term `1`, so it is a unit of
`ℝ[y]⟦z⟧`). -/
theorem eq_51 (n : ℕ) (x : ℝ) (hp0 : 0 < critP n x) (hp1 : critP n x < 1) :
    let w : ℝ := critP n x / (1 - critP n x)
    Hpoly n x =
      Polynomial.C ((2 : ℝ) ^ n * (n.factorial : ℝ) / (1 + w) ^ (n * (n - 1))) *
        PowerSeries.coeff n
          (expHadamard (expOf (-((1 / 2 : ℚ) • doubleArg (SExcess w)))) (I0 (Polynomial.C w)) *
            PowerSeries.invOfUnit (expHadamard (expOf (-SExcess w)) (D0 (Polynomial.C w))) 1) := by sorry

end Random2SATWindow.CriticalLaw
