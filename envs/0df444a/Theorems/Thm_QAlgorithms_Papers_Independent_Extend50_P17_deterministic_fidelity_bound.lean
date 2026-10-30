-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_deterministic_fidelity_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.deterministic_fidelity_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:50:31.018295+00:00
-- url     : https://prove2.me/theorems/80923982-3396-4b73-9204-e9c6d33cdd09
-- title:
--   Theorem 2 / Eq.(9): deterministic MPBT fidelity bound (seed headline)
-- statement:
--   Let $d,k\ge1$ be integers. Alice and Bob share $N$ normalized maximally entangled pairs of local dimension $d$. Alice uses the square-root measurement for the ordered-port signals, completed on its kernel; Bob selects distinct ports and reorders them. Let $F_d(N,k)$ denote the entanglement fidelity, measured using $k$ maximally entangled reference pairs. For $2k\le N$,
--
--   $$F_d(N,k)\ge\frac{\binom Nk}{\binom{d^2+N-1}k}\ge\left(1-\frac{d^2-1}{d^2+N-k}\right)^k.$$
--
--   For each fixed $d,k$ there are $C>0$ and $N_0$ such that $|1-F_d(N,k)|\le C/N$ for every $N\ge N_0$, and $F_d(N,k)\to1$. This is the deterministic fixed-resource fidelity guarantee.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 4, Theorem 2 / Eq.(9): deterministic MPBT fidelity bound (seed headline)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.4, Theorem 2, Eq.(9): both lower bounds and the full fixed-k conclusion. -/
theorem deterministic_fidelity_bound (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (∀ N : ℕ, 2 * k ≤ N →
      binomialBound d N k ≤ mpbtFidelity d N k ∧ powerBound d N k ≤ binomialBound d N k) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N ≥ N0,
      |1 - mpbtFidelity d N k| ≤ C / (N : ℝ)) ∧
    Tendsto (fun N => mpbtFidelity d N k) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
