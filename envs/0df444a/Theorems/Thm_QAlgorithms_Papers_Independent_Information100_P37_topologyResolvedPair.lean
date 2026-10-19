-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_topologyResolvedPair
-- name    : QAlgorithms.Papers.Independent.Information100.P37.topologyResolvedPair
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:20:18.946865+00:00
-- url     : https://prove2.me/theorems/8ca335a9-002b-465b-b63c-6ed0ff40004c
-- title:
--   Proposition 19, Topology-resolved equal-CGP pair
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Use vertices $0,\ldots,5$ for the complete graph $K_6$ and star $S_6$, with hub $0$. For either adjacency matrix $A$, define $U(t)=\exp[-itA/\|A\|_{\rm op}]$, where the norm is spectral. At
--   $$t_K=\frac56\arccos\left(\frac{3\sqrt{145}}{25}-2\right),\qquad t_S=\pi,$$
--   $$C_K=C_S=\frac{16}{175},\qquad \Delta_K=\frac{16\sqrt{10}}{875},\qquad \Delta_S=\frac{4\sqrt{230}}{875},\qquad \Delta_S^2=\frac{23}{16}\Delta_K^2.$$
--   Their response matrices are $G_K=(96/125)H_6$ and $G_S=(24/25)(0\oplus H_5)$, and
--   $$X_K(p)=\frac{96}{125}\left(\sum_{j=0}^5p_j^2-\frac16\right),\quad X_S(p)=\frac{24}{25}\left(\sum_{j=1}^5p_j^2-\frac{(\sum_{j=1}^5p_j)^2}{5}\right).$$
--
--   The exact matched pair resolves topology-dependent selectivity beyond average coherence.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 10, Proposition 19, Topology-resolved equal-CGP pair

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF pp.10--11, Proposition 19, (88)--(95): exact spectral-normalized graph comparison. -/
theorem topologyResolvedPair :
    let tk := (5 / 6 : ℝ) * Real.arccos (3 * Real.sqrt 145 / 25 - 2)
    let UK := walk (completeAdjacency 6) tk
    let US := walk (starAdjacency 6) Real.pi
    cgp (conjSuperop UK) = 16 / 175 ∧ cgp (conjSuperop US) = 16 / 175 ∧
    cgpd (conjSuperop UK) = 16 * Real.sqrt 10 / 875 ∧ cgpd (conjSuperop US) = 4 * Real.sqrt 230 / 875 ∧
    cgpd (conjSuperop US) ^ 2 = (23 / 16 : ℝ) * cgpd (conjSuperop UK) ^ 2 ∧
    response UK = (96 / 125 : ℝ) • zeroSumProjector (Fin 6) ∧
    response US = (24 / 25 : ℝ) • leafProjector 6 ∧
    (∀ p : Fin 6 → ℝ, IsPopulation p →
      generated (conjSuperop UK) p = (96 / 125 : ℝ) * ((∑ j, p j ^ 2) - 1 / 6) ∧
      generated (conjSuperop US) p = (24 / 25 : ℝ) *
        ((∑ j : Fin 6, if j.val = 0 then 0 else p j ^ 2) -
          (∑ j : Fin 6, if j.val = 0 then 0 else p j) ^ 2 / 5)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
