-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_qubitRelation
-- name    : QAlgorithms.Papers.Independent.Information100.P37.qubitRelation
-- status  : Disproved
-- author  : @Goku
-- created : 2026-10-19T11:11:09.993296+00:00
-- url     : https://prove2.me/theorems/e008cb0e-e1bd-49e5-93e1-2265faad71de
-- title:
--   Corollary 11, Qubit relation
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   For a two-dimensional unitary,
--   $$\Delta_U=\frac2{\sqrt5}C_U,\qquad\Xi_U=0,$$
--   where $\Xi_U^2=(2\|A\|_F^2+6\|\operatorname{diag}A\|_2^2)/D_2$ and $A=G-\operatorname{Tr}(G)H_2$. For $R(\theta)=\begin{pmatrix}\cos\theta&-\sin\theta\\\sin\theta&\cos\theta\end{pmatrix}$,
--   $$C_{R(\theta)}=\frac{\sin^2(2\theta)}6,\qquad \Delta_{R(\theta)}=\frac{\sin^2(2\theta)}{3\sqrt5}.$$
--   These formulas include incoherent rotations, for which both quantities vanish.
--
--   The one-dimensional population-contrast space leaves no qubit anisotropy.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 6, Corollary 11, Qubit relation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF pp.6--7,15, Corollary 11 and (49): all qubit gates, including monomial ones. -/
theorem qubitRelation (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    cgpd (conjSuperop U) = (2 / Real.sqrt 5) * cgp (conjSuperop U) ∧
    excess (response U) = 0 ∧
    (∀ t : ℝ, cgp (conjSuperop (((rotY (2 * t)).submatrix (fun i : Fin 2 => i.val == 1) (fun j : Fin 2 => j.val == 1)))) = Real.sin (2 * t) ^ 2 / 6 ∧
      cgpd (conjSuperop (((rotY (2 * t)).submatrix (fun i : Fin 2 => i.val == 1) (fun j : Fin 2 => j.val == 1)))) = Real.sin (2 * t) ^ 2 / (3 * Real.sqrt 5)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
