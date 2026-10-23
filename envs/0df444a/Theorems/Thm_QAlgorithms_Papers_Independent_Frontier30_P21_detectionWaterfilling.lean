-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P21_detectionWaterfilling
-- name    : QAlgorithms.Papers.Independent.Frontier30.P21.detectionWaterfilling
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:21:45.089993+00:00
-- url     : https://prove2.me/theorems/2cc2217b-6aec-4992-b9cc-f0d3e1840352
-- title:
--   Attained finite-grid optimization of the printed receiver objective
-- statement:
--   Let $\hbar>0$, $\Delta\omega>0$, and $\omega_c>0$. Suppose $m\geq1$ is the number of admitted grid modes, so $m\Delta\omega\leq\omega_c<(m+1)\Delta\omega$, and put $\omega_k=k\Delta\omega$ for $1\leq k\leq m$. Let $D_c\in(0,1]$ and $\eta_k=D_c(\omega_k/\omega_c)^2$. Choose $\xi=1/2$ or $\xi=1$ and a finite mean energy $E\geq0$. Optimize the explicitly printed numerical objective
--
--   $$
--   J(N)=\sum_{k=1}^m\xi\log_2\!\left(1+\frac{\eta_k N_k}{\xi^2}\right),\qquad
--   N_k\geq0,\quad \sum_{k=1}^m\hbar\omega_kN_k=E.
--   $$
--
--   If $E=0$, the all-zero allocation is optimal. If $E>0$, there exists $\beta>0$ for which the allocation
--
--   $$
--   N_k(\beta)=\max\!\left\{\frac1{\beta\hbar\omega_k}-\frac{\xi^2}{\eta_k},0\right\}
--   $$
--
--   is feasible and maximizes $J$ over all feasible allocations. Moreover, with $\omega_0=\xi^2\beta\hbar\omega_c^2/D_c$,
--
--   $$
--   N_k(\beta)>0\iff\omega_k>\omega_0,\qquad
--   N_k(\beta)=0\iff\omega_k\leq\omega_0.
--   $$
--
--   This is the finite numerical optimization behind the spectral-allocation plot. It requires no continuum approximation and makes no claim that the printed homodyne objective is achieved by the circular Gaussian ensemble of Eq. (6).
--
--   **Formalization Note** The multiplier absorbs the common factor $\xi/\ln2$. The quadratic transmissivity is treated as the explicit numerical model, independently of the unquantified physical far-field approximation.
-- source:
--   Classical capacity of the lossy bosonic channel: the exact solution, arXiv:quant-ph/0308012v2, PDF p. 4, Paragraph following Fig.2, allocation for Eq.(11)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P21

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.4, allocation following Fig.2: the finite positive grid up to cutoff
has an attained optimum for (11), with the printed water-filling allocation.
The strict active-frequency threshold includes its zero-allocation boundary.
The zero-energy case uses the zero allocation without beta division.
This is the numerical optimization only; no continuum replacement is used. -/
theorem detectionWaterfilling (m : ℕ) (hm : 0 < m)
    (hbar spacing cutoff Dc xi E : ℝ)
    (hhbar : 0 < hbar) (hspacing : 0 < spacing) (hcutoff : 0 < cutoff)
    (hgridLow : (m : ℝ) * spacing ≤ cutoff)
    (hgridHigh : cutoff < ((m : ℝ) + 1) * spacing)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hxi : xi = 1 / 2 ∨ xi = 1) (hE : 0 ≤ E) :
    (E = 0 → OptimalAllocation (m := m) hbar spacing cutoff Dc xi E (fun _ => 0)) ∧
    (0 < E → ∃ beta : ℝ, 0 < beta ∧
      OptimalAllocation hbar spacing cutoff Dc xi E
        (receiverAllocation (m := m) hbar spacing cutoff Dc xi beta) ∧
      ∀ i : Fin m,
        (0 < receiverAllocation hbar spacing cutoff Dc xi beta i ↔
          xi ^ 2 * beta * hbar * cutoff ^ 2 / Dc < gridFrequency spacing i) ∧
        (receiverAllocation hbar spacing cutoff Dc xi beta i = 0 ↔
          gridFrequency spacing i ≤ xi ^ 2 * beta * hbar * cutoff ^ 2 / Dc)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P21

end
