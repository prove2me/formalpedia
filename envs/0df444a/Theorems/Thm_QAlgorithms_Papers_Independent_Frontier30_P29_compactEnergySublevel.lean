-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P29_compactEnergySublevel
-- name    : QAlgorithms.Papers.Independent.Frontier30.P29.compactEnergySublevel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:54:51.853983+00:00
-- url     : https://prove2.me/theorems/f897430f-6680-4c03-a366-c10136ef76fe
-- title:
--   Trace-norm compactness of an energy sublevel
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space and let $F$ be a positive selfadjoint observable with a complete orthonormal eigenbasis $(e_j)_{j\ge0}$. List its nonnegative eigenvalues $f_j$ with multiplicity, and suppose $f_j\to+\infty$. For $E>0$, let $\mathcal S_E$ consist of positive trace-class operators $S$ with trace one and extended mean energy at most $E$. Then
--
--   $$
--   \mathcal S_E=\left\{S:\operatorname{Tr}S=1,\ S\ge0,\ \sum_{j=0}^{\infty}f_j\langle e_j,S e_j\rangle\le E\right\}
--   \quad\text{is compact in the trace norm.}
--   $$
--
--   The energy sum is nonnegative and may be infinite before imposing the constraint. The assertion includes an empty sublevel and requires neither a channel nor Gibbs summability. It supplies the compact state domain used for capacity attainment.
--
--   **Formalization Note** A complete countable eigenbasis and eigenvalues represent the possibly unbounded diagonal observable. Repeating eigenvalues according to finite multiplicity makes escape to infinity equivalent to the printed spectral hypothesis. The state space, extended energy sum, and trace-norm topology are reused from the accepted operator library.
-- source:
--   Entanglement-assisted capacity of constrained quantum channel, arXiv:quant-ph/0211170v2, PDF p. 10, §3, unnumbered Lemma (proof on PDF p.11)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P29

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State spectralEnergy TraceCompactStates)

namespace QAlgorithms.Papers.Independent.Frontier30.P29

/-- Unnumbered Lemma, PDF pp.10--11 of arXiv:quant-ph/0211170v2.
A complete eigenbasis `b` and nonnegative eigenvalues `energy` represent the
positive selfadjoint constraint observable. Escape to infinity, with eigenvalues
listed with multiplicity, expresses the printed discrete-spectrum and finite-
multiplicity hypotheses. The normalized density operators of energy at most
`E > 0` form a compact set in trace norm, including when that set is empty.
No channel, feasibility assumption, or Gibbs summability is required. -/
theorem compactEnergySublevel
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℂ H) (energy : ℕ → NNReal)
    (hescape : Tendsto (fun j => (energy j : ℝ)) atTop atTop)
    (E : ℝ) (hE : 0 < E) :
    TraceCompactStates (b := b)
      {rho : State b | spectralEnergy b energy rho ≤ ENNReal.ofReal E} := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P29

end
