-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapD09_worstCaseOPI_balanced
-- name    : QAlgorithms.Papers.RoadmapD09.worstCaseOPI_balanced
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:44:42.836328+00:00
-- url     : https://prove2.me/theorems/edbeefeb-aa5a-4a0e-916d-085d412496e0
-- title:
--   Worst-case quantum OPI beyond DQI: balanced two-branch guarantee
-- statement:
--   Consider a growing public parameter family \(n_j,k_j,p_j,e_j\), where \(p_j\) is prime, \(e_j\ge1\), \(n_j,k_j>0\), \(n_j/2\le k_j\le n_j\le q_j=p_j^{e_j}\), and \(n_j,p_j\to\infty\). Put \(R_j=k_j/n_j\). Assume \(\log_2 q_j\le Cn_j^a\) eventually for fixed \(C>0\) and \(a\in\mathbb N\). Each \(\mathbb F_{q_j}\) has its standard effective polynomial-basis binary representation, specified by its characteristic, extension degree and irreducible modulus. Fix a target \(s\) and assume one of these two eventual regimes, with a common fixed margin \(c>0\):
--
--   1. \(s=1\) and \(R_j\ge3/4+c\).
--   2. \(1/2<s<1\), \(R_j\le3/4\), and
--   $$
--   R_j\ge1-\left(\sqrt{s/2}+\sqrt{(1-s)/2}\right)^4+c,\qquad
--   H_2(R_j)+R_j\log_2\left(3\left(\frac{2s-1}{\sqrt3}\right)^{1/(1-R_j)}\right)\le-c.
--   $$
--   Here \(H_2(t)=-t\log_2t-(1-t)\log_2(1-t)\), with \(0\log_20=0\).
--
--   Let \(\beta:\mathbb N\to[0,\infty)\) tend to zero. There exist a uniform quantum oracle solver, a polynomial \(w\) and an index \(j_0\) such that, for every \(j\ge j_0\), every tuple of distinct evaluation points \(\alpha_1,\ldots,\alpha_{n_j}\in\mathbb F_{q_j}\), and every hidden subset family satisfying
--   $$
--   \max_i\left|\frac{|S_i|}{q_j}-\frac12\right|\le\beta(n_j),
--   $$
--   the solver outputs a polynomial \(P\in\mathbb F_{q_j}[X]\) for which
--   $$
--   \Pr\!\left[\deg P<k_j\ \text{and}\
--   |\{i:P(\alpha_i)\in S_i\}|\ge s n_j\right]\ge\frac23,
--   \qquad
--   \operatorname{work}\le w(n_j).
--   $$
--   Its classical constructor receives only the public field description, \(n_j,k_j\), the evaluation points and the integer target \(\lceil s n_j\rceil\). The sets are accessed through their individual quantum XOR membership oracles. Work counts queries, standard Clifford+T gates, measurements, preparations, classical control, workspace and coefficient decoding; constructor time and space are polynomial in \(n_j+\log q_j\). The constants and threshold are uniform over evaluation points and hidden sets, and probability refers to internal coins and measurements.
--
--   This gives an algorithm on every promised instance, including exact perfect satisfaction in the first branch. No random-instance assumption, efficient-decoder hypothesis, or pre-existing-solution hypothesis is imposed.
--
--   **Formalization Note** The asymptotic reading makes the \(\log q\) bound and high-rate constant margin explicit using Theorem 6.1 and Remark 6.2. The printed informal high-rate sentence omits them. Unequal densities are retained under footnote 3. Rates tending to one and \(R_j=1\) are retained through constructive dimension reduction. These bridges require independent mathematical moderation.
-- source:
--   Worst-Case Quantum Algorithm for Optimal Polynomial Intersection Beyond Decoded Quantum Interferometry, arXiv:2607.14650v1, Theorem 1.1 (continues on PDF p.5), PDF p. 4. https://arxiv.org/abs/2607.14650v1 . PDF SHA-256: 8aa48139dfaf7a4738d0f1d2ed4ed65a2271972df11fda0c79041478b71b9bad.

import Definitions.Def_QAlgorithms_Defs_BalancedOPIRegimes
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_RoadmapD09_Model
set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix

namespace QAlgorithms.Papers.RoadmapD09

open QAlgorithms OPI









/-- Theorem 1.1 (balanced case), arXiv:2607.14650v1, PDF pp.4–5 (printed pp.2–3).
Both branches are encoded by BalancedAlgorithmicRegime: s = 1 with a positive
rate gap above 3/4, or 1/2 < s < 1 with R ≤ 3/4 and positive constant margins
in (1) and (2), with base-2 log and the entire 3 times real-power expression inside log.
The formal interpretation uses Theorem 6.1 and Remark 6.2 (PDF pp.38–39):
log q is polynomially bounded in n; p tends to infinity. This makes explicit
assumptions omitted from the first informal clause. Unequal densities tending
uniformly to 1/2 implement footnote 3, PDF p.4. High rates up to and including
R = 1 are retained by lowering the working dimension to min(k, floor(7n/8)).
The solver and its resource polynomial and threshold precede every evaluation
tuple and hidden set family; success is at least 2/3 on each promised input.
The deterministic polynomial-time dual GRS list decoder is supplied by §2.3
and §6.1 (PDF pp.19,39), not assumed as a black-box success hypothesis. -/
theorem worstCaseOPI_balanced
    (n k p e : ℕ → ℕ) (s : ℝ)
    (hregime : BalancedAlgorithmicRegime n k p e s)
    (F : ℕ → Type) [∀ j, Field (F j)] [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)]
    (E : (j : ℕ) → publicFieldEncoding (F j))
    (hp : ∀ j, (E j).p = p j) (he : ∀ j, (E j).e = e j)
    (heffective : ∀ j, EffectiveFieldEncoding (E j))
    (beta : ℕ → ℝ) (hbeta : ∀ t, 0 ≤ beta t)
    (hbetaLimit : Filter.Tendsto beta Filter.atTop (nhds 0)) :
    ∃ A : UniformSolver F n k E, ∃ work : Polynomial ℕ, ∃ j0 : ℕ,
      ∀ j ≥ j0, ∀ alpha : Fin (n j) → F j, Function.Injective alpha →
        ∀ sets : Fin (n j) → Finset (F j),
          (∀ i, |((sets i).card : ℝ) / Fintype.card (F j) - 1 / 2| ≤ beta (n j)) →
          let Q : PublicInput F n := ⟨j, alpha, ⌈s * (n j : ℝ)⌉₊⟩
          solverSuccess A Q sets ≥ 2 / 3 ∧ solverWork A Q sets ≤ work.eval (n j) := by sorry

end QAlgorithms.Papers.RoadmapD09
