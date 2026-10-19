-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapD03_weightedDQI_optimalExpectation
-- name    : QAlgorithms.Papers.RoadmapD03.weightedDQI_optimalExpectation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:43:47.390548+00:00
-- url     : https://prove2.me/theorems/d46378ab-3ff4-4724-ac55-54b0b7aaf584
-- title:
--   Multivariate DQI: asymptotically optimal weighted expectation
-- statement:
--   Let $p$ be prime and $1\le r<p$. Let $B\in\mathbb F_p^{m\times n}$ with $m>0$, and let $L_i\subseteq\mathbb F_p$ have cardinality $r$. Define $f_i(y)=1$ on $L_i$ and $f_i(y)=-1$ otherwise. Partition $[m]$ into nonempty blocks $S_1,\ldots,S_N$, write $m_t=|S_t|$, and assign positive weights $g_t$. Put $F_t(x)=\sum_{i\in S_t}f_i(b_i\cdot x)$ and $F_g(x)=\sum_t g_tF_t(x)$, where $b_i$ is row $i$ of $B$ and $x\in\mathbb F_p^n$.
--
--   Fix an exact degree ratio $\mu=\ell/m\in(0,1/2)$, with integer $\ell$, and assume $2\ell+1<d^\perp$, where $d^\perp$ is the minimum nonzero Hamming weight in $\ker B^\top$ (infinite when this kernel is zero). Let $E_{\mathrm{opt}}$ be the supremum of $\sum_x|\psi_P(x)|^2F_g(x)$ over complex multivariate polynomials of total degree at most $\ell$ such that $\psi_P(x)=P(F_1(x),\ldots,F_N(x))$ has unit norm. This supremum is attained by an admissible polynomial.
--
--   Write $\bar f=2r/p-1$, $\sigma=2\sqrt{r(p-r)}/p$, $\kappa=(p-2r)/\sqrt{r(p-r)}$, and define
--   $$
--   \Gamma_{g,m,\kappa}(\mu)=\sup_{\substack{0\le\alpha_t\le1\ (1\le t\le N)\\\sum_t(m_t/m)\alpha_t\le\mu}}\sum_t\frac{m_t}{m}g_t\left(\kappa\alpha_t+2\sqrt{\alpha_t(1-\alpha_t)}\right).
--   $$
--   For each fixed $\kappa$, there are $C_\kappa>0$ and an integer $m_0$, chosen before all other instance data and $\mu$, such that every admissible instance with $m\ge m_0$ satisfies
--   $$
--   \frac{E_{\mathrm{opt}}}{m}=\bar f\sum_t\frac{g_tm_t}{m}+\sigma\Gamma_{g,m,\kappa}(\mu)+R,
--   \qquad |R|\le\frac{C_\kappa}{m}\sum_tg_tm_t^{3/4}.
--   $$
--   Along any admissible family with fixed $\kappa,\mu,N$, unbounded $m$, and eventually bounded $\max_tg_t$, the residual $R$ tends to zero. No convergence of block proportions is required.
--
--   This characterizes the asymptotically optimal signed weighted objective among multivariate DQI states. It does not impose decoder access or a preparation complexity bound.
--
--   **Formalization Note** The range $1\le r<p$ is explicitly recalled by Appendix A (PDF p.30) and is carried as a standing assumption although omitted from the printed theorem sentence. Exact integer pairs $(\ell,m)$ are used; no rounding convention is added.
-- source:
--   Multivariate Decoded Quantum Interferometry for Weighted Optimization, arXiv:2605.10666v2, Theorem 2 (Asymptotically Optimal Expectation Value), equations (9)–(10), PDF p. 6. https://arxiv.org/abs/2605.10666v2 . PDF SHA-256: 06d8922afdaab0f45163cdc89a0d47c68172651c5149f375f474f57a4e022c8b.

import Definitions.Def_QAlgorithms_Defs_WeightedDQI
import Definitions.Def_QAlgorithms_Defs_DQI
import Definitions.Def_QAlgorithms_Papers_RoadmapD03_Model
set_option autoImplicit false

noncomputable section

open Filter

namespace QAlgorithms.Papers.RoadmapD03

open QAlgorithms.WeightedDQI






/-- Theorem 2 (Asymptotically Optimal Expectation Value), arXiv:2605.10666v2,
PDF p.6, equations (9)–(10), proved in Appendix A, PDF pp.30–38.
The printed theorem omits the clause-size range; `ClauseDomain` carries
`1 ≤ r < p` explicitly declared on p.30. No formula is changed.
The constants depend only on kappa and precede all uniform instance data.
The final clause is convergence of the remainder, with fixed block count and
eventually bounded weights, and does not require limiting block proportions. -/
theorem weightedDQI_optimalExpectation :
    ∀ kappa : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ m0 : ℕ,
      (∀ mu : ℝ, 0 < mu → mu < 1 / 2 → ∀ I : WeightedInstance kappa mu,
        (letI : NeZero I.clauses.p := ⟨I.clauses.prime.ne_zero⟩
          ∃ P : MvPolynomial (Fin I.blocks) ℂ,
            P.totalDegree ≤ I.ell ∧ IsState (state I.B I.L I.partition P) ∧
            polynomialExpectation I P = weightedOptimalValue I) ∧
        (m0 ≤ I.m → |residual I| ≤ C * errorScale I)) ∧
      (∀ (N : ℕ) (mu : ℝ), 0 < mu → mu < 1 / 2 →
        ∀ family : ℕ → WeightedInstance kappa mu,
          (∀ j, (family j).blocks = N) →
          Tendsto (fun j => (family j).m) atTop atTop →
          (∃ G : ℝ, 0 < G ∧ ∀ᶠ j in atTop,
            ∀ t, (family j).partition.weights t ≤ G) →
          Tendsto (fun j => residual (family j)) atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.RoadmapD03
