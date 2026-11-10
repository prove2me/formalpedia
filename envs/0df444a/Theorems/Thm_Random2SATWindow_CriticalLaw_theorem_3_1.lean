-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_theorem_3_1
-- name    : Random2SATWindow.CriticalLaw.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:07.237254+00:00
-- url     : https://prove2.me/theorems/3c2d8b3f-2e11-42e7-9000-867e12c0f110
-- title:
--   Theorem 3.1 — critical window of random 2-SAT: $P(F(n,\lfloor n+xn^{2/3}\rfloor)\in\mathrm{SAT})\to f(x)=\sum_q\pi_q(x)$ locally uniformly, with the profile's shape and tails
-- statement:
--   For every real $x$, the limit
--   $$f(x)=\lim_{n\to\infty}P\big(F(n,m=\lfloor n+xn^{2/3}\rfloor)\in\mathrm{SAT}\big)$$
--   exists and admits an explicit convergent Airy representation:
--   $$f(x)=\sum_{q\ge0}\pi_q(x),\qquad\pi_0(x)=2^{-1/6}Q_{1/2;0}(x;\emptyset),$$
--   where the $\pi_q(x)$ are specified in (126). The function $f:\mathbb R\to(0,1)$ is continuous and nonincreasing. Convergence is locally uniform in $x$, and the same limit holds for the independent-clause model with $p=\frac{1+xn^{-1/3}}{2n}$. Numerical evaluation gives $f(0)\approx0.906\,224$. Moreover,
--   $$x\to-\infty:\ 1-f(x)=\frac1{16|x|^3}-\frac{113}{512|x|^6}+O(|x|^{-9}),\qquad x\to+\infty:\ f(x)\to0,\quad-\log f(x)\le\frac{x^3}6+O(x).$$
--
--   In Lean, twelve clauses: the fixed-size probabilities converge locally uniformly to $f$ = `fProfile`; the series $\sum_q\pi_q(x)$ has sum $f(x)$ (`HasSum`), and every integrand of (126) is integrable; $\pi_0=2^{-1/6}Q_{1/2;0}(\cdot;\emptyset)$; $0<f<1$; $f$ is continuous; $f$ is nonincreasing; the independent-clause probabilities converge locally uniformly to $f$; $|f(0)-0.906224|\le5\cdot10^{-7}$; the left-tail expansion with an explicit $O(|x|^{-9})$; $f(x)\to0$ as $x\to+\infty$; and $-\log f(x)\le x^3/6+Cx$ for large $x$.
--
--   Differences from the source:
--   - reading: 'Numerical evaluation gives f(0) ≈ 0.906 224' → |fProfile 0 − 0.906224| ≤ 5/10⁷; reason: six printed decimals read as correct rounding (the BRIEF's pinned reading)
--   - encoding: 'the limit f(x) = lim_n P(F(n, ⌊n + xn^{2/3}⌋) ∈ SAT) exists … f(x) = Σ_{q≥0} π_q(x) … convergence is locally uniform' → TendstoLocallyUniformly (n, x) ↦ satProbUniform n (critM n x) to fProfile, and HasSum (q ↦ piQC q x) (fProfile x) in ℂ; reason: f is defined as the series, so existence of the limit and its identification with the convergent series are both clauses
--   - encoding: 'explicit convergent Airy representation', π_q specified in (126) → ∀ q x, Integrable (piIntegrand q x); reason: absolute convergence of every (126) integral, so no Bochner-integral junk value enters
--   - encoding: O(|x|^{−9}) as x → −∞; O(x) as x → +∞ → ∃ C X0, ∀ x ≤ −X0, |1 − f(x) − (1/(16|x|³) − 113/(512|x|⁶))| ≤ C/|x|⁹; ∃ C X0, ∀ x ≥ X0, −log f(x) ≤ x³/6 + C x; reason: explicit forms of O(·): two-sided for the expansion, one-sided as printed for −log f
--   - encoding: m = ⌊n + x n^{2/3}⌋ → critM n x = Int.toNat ⌊n + x n^{2/3}⌋; reason: negative only for finitely many n on each compact x-set, so the locally uniform limit is unchanged
--   - encoding: π_q(x) given by the integral (126) → piQC q x : ℂ is (126) verbatim; piQ q x = Re piQC q x, fProfile x = Σ' q, piQ q x; reason: (126) is a complex integral; Theorem 5.1(i) (theorem_5_1_i) states it is real
--   - encoding: Π with any fixed c > 0 in (30), (32) → contourPi with c = 1 (rays 1 + t e^{±iπ/3}, t > 0); reason: the paper notes the value does not depend on c > 0
--   - encoding: 2-SAT formulas: sets of distinct legal clauses on two distinct variables; F(n, p) independent clauses, F(n, m) uniform m-subsets of the N_n = 2n(n−1) legal clauses → LegalClause n = unordered pairs (Sym2) of literals Fin n × Bool whose variables differ, Formula n = Finset (LegalClause n); probBinom n p E = Σ_{F ∈ E} p^{|F|}(1−p)^{N_n−|F|}, satProbUniform n m = #{F : |F| = m, F ∈ SAT}/C(N_n, m); reason: the paper's model verbatim; N_n = Fintype.card (LegalClause n) = 2n(n−1)
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Theorem 3.1, printed p. 9 (PDF 11); proof §5.1, printed pp. 20–59 (PDF 22–61)

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

/-- **Theorem 3.1** (critical window of random 2-SAT, printed p. 9 / PDF 11). For every real
`x` the limit `f(x) = lim_n P(F(n, m = ⌊n + x n^{2/3}⌋) ∈ SAT)` exists, locally uniformly in `x`,
and equals the convergent Airy series `f(x) = Σ_{q ≥ 0} π_q(x)` with `π_q` given by (126) (each
integral absolutely convergent) and `π_0(x) = 2^{-1/6} Q_{1/2;0}(x; ∅)`. The function
`f : ℝ → (0, 1)` is continuous and nonincreasing; the same locally uniform limit holds for the
independent-clause model with `p = (1 + x n^{-1/3})/(2n)`; `f(0) ≈ 0.906224` (six decimals);
as `x → -∞`, `1 - f(x) = 1/(16|x|³) - 113/(512|x|⁶) + O(|x|^{-9})`; as `x → +∞`, `f(x) → 0`
and `-log f(x) ≤ x³/6 + O(x)`. -/
theorem theorem_3_1 :
    TendstoLocallyUniformly (fun (n : ℕ) (x : ℝ) => satProbUniform n (critM n x)) fProfile
      atTop ∧
    (∀ x : ℝ, HasSum (fun q : ℕ => piQC q x) (fProfile x : ℂ)) ∧
    (∀ (q : ℕ) (x : ℝ), Integrable (piIntegrand q x)) ∧
    (∀ x : ℝ, piQC 0 x = (((2 : ℝ) ^ (-(1 / 6 : ℝ)) : ℝ) : ℂ) * quotientQ (1 / 2) 0 ![] x) ∧
    (∀ x : ℝ, 0 < fProfile x ∧ fProfile x < 1) ∧
    Continuous fProfile ∧ Antitone fProfile ∧
    TendstoLocallyUniformly (fun (n : ℕ) (x : ℝ) => satProbBinom n (critP n x)) fProfile atTop ∧
    |fProfile 0 - 0.906224| ≤ 5 / 10 ^ 7 ∧
    (∃ C X0 : ℝ, ∀ x : ℝ, x ≤ -X0 →
      |1 - fProfile x - (1 / (16 * |x| ^ 3) - 113 / (512 * |x| ^ 6))| ≤ C / |x| ^ 9) ∧
    Tendsto fProfile atTop (𝓝 0) ∧
    (∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → -Real.log (fProfile x) ≤ x ^ 3 / 6 + C * x) := by sorry

end Random2SATWindow.CriticalLaw
