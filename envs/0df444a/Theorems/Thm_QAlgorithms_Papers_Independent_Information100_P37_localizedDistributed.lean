-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_localizedDistributed
-- name    : QAlgorithms.Papers.Independent.Information100.P37.localizedDistributed
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:19:33.30612+00:00
-- url     : https://prove2.me/theorems/a602431a-64eb-435e-99d4-8d04bb4cbd6b
-- title:
--   Proposition 18, Localized versus distributed population modes
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   In dimension four, let $R(\theta)=\begin{pmatrix}\cos\theta&-\sin\theta\\\sin\theta&\cos\theta\end{pmatrix}$, $U_{\rm loc}=R(\pi/4)\oplus I_2$, and $U_{\rm dis}=R(\pi/8)\oplus R(\pi/8)$. These constructed matrices are unitary and satisfy
--   $$C_{\rm loc}=C_{\rm dis}=\frac1{20},\qquad \Delta_{\rm loc}^2=\frac{13}{2800},\qquad \Delta_{\rm dis}^2=\frac1{600}.$$
--   For every simplex population,
--   $$X_{\rm loc}(p)=\frac{(p_1-p_2)^2}2,\qquad X_{\rm dis}(p)=\frac{(p_1-p_2)^2+(p_3-p_4)^2}4.$$
--   The response matrices are
--   $$G_{\rm loc}=\tfrac12\begin{pmatrix}1&-1&0&0\\-1&1&0&0\\0&0&0&0\\0&0&0&0\end{pmatrix},\qquad G_{\rm dis}=\tfrac14\begin{pmatrix}1&-1&0&0\\-1&1&0&0\\0&0&1&-1\\0&0&-1&1\end{pmatrix}.$$
--   Their $(\operatorname{Tr}G,\operatorname{Tr}G^2,\|\operatorname{diag}G\|_2^2)$ triples are $(1,1,1/2)$ and $(1,1/2,1/4)$, and their second moments are $1/140$ and $1/240$.
--
--   The calibration separates localized and distributed population response at the same mean.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 10, Proposition 18, Localized versus distributed population modes

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF pp.10,15, Proposition 18, (82)--(86),(F2): constructed four-level calibration. -/
theorem localizedDistributed :
    localized ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧ distributed ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
    cgp (conjSuperop localized) = 1 / 20 ∧ cgp (conjSuperop distributed) = 1 / 20 ∧
    cgpd (conjSuperop localized) ^ 2 = 13 / 2800 ∧ cgpd (conjSuperop distributed) ^ 2 = 1 / 600 ∧
    moment (conjSuperop localized) 2 = 1 / 140 ∧ moment (conjSuperop distributed) 2 = 1 / 240 ∧
    response localized = (1 / 2 : ℝ) • !![1,-1,0,0; -1,1,0,0; 0,0,0,0; 0,0,0,0] ∧
    response distributed = (1 / 4 : ℝ) • !![1,-1,0,0; -1,1,0,0; 0,0,1,-1; 0,0,-1,1] ∧
    ((response localized).trace, (response localized * response localized).trace,
      diagonalSq (response localized)) = (1, 1, 1 / 2) ∧
    ((response distributed).trace, (response distributed * response distributed).trace,
      diagonalSq (response distributed)) = (1, 1 / 2, 1 / 4) ∧
    (∀ p : Fin 4 → ℝ, IsPopulation p →
      generated (conjSuperop localized) p = (p 0 - p 1) ^ 2 / 2 ∧
      generated (conjSuperop distributed) p = ((p 0 - p 1) ^ 2 + (p 2 - p 3) ^ 2) / 4) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
