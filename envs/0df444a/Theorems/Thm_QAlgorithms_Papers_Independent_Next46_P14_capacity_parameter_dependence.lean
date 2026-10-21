-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_capacity_parameter_dependence
-- name    : QAlgorithms.Papers.Independent.Next46.P14.capacity_parameter_dependence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:14:45.224917+00:00
-- url     : https://prove2.me/theorems/7fcc63e1-ee9d-46a5-a5f4-57f810f2853e
-- title:
--   Dependence of SPIR capacity on message and server counts
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. The available entropy budget is $H_p(S)\leq\rho L\max_i\ell_i$, with unused randomness allowed. Operational sequences have growing admissible blocklengths, exact privacy at every blocklength, and decoding error tending to zero for each request. The capacity region is the closure of simultaneous nonnegative lower rate guarantees, adjoining the zero vector in infeasible cases. For equal messages with $K,N\geq2$ and $\rho\geq0$, changing K while fixing the field, N, and budget leaves capacity unchanged. Increasing N strictly increases capacity whenever the initial capacity is positive. For a fixed field and K and any fixed $\rho>0$,
--
--   $$\lim_{N\to\infty} C_{\rm SPIR}(K,N,p,\rho)=1.$$
--
--   The positive-budget guard on the limit preserves the source’s nonzero-capacity qualification; zero budget has zero capacity at every N.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 5, Observations 2–3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Observations 2–3, PDF p.5: independence of K≥2, strict increase in N
when the initial spirCapacity is positive, and convergence to one for fixed rho>0. -/
theorem capacity_parameter_dependence (m : SpirParameters) (hK : 2 ≤ m.K) (hN : 2 ≤ m.N)
    (hequal : ∀ k, m.ell k = 1) (rho : ℝ) (hrho : 0 ≤ rho) :
    (∀ m2 : SpirParameters, m2.p = m.p → m2.N = m.N → 2 ≤ m2.K →
      (∀ k, m2.ell k = 1) → spirCapacity m2 rho = spirCapacity m rho) ∧
    (∀ (N2 : ℕ) (hN2 : 0 < N2), m.N < N2 → 0 < spirCapacity m rho →
      spirCapacity m rho < spirCapacity
        (equalParameters m.p m.prime m.K N2 m.K_pos hN2) rho) ∧
    (0 < rho → Filter.Tendsto
      (fun t : ℕ => spirCapacity
        (equalParameters m.p m.prime m.K (t + 2) m.K_pos (by omega)) rho)
      Filter.atTop (nhds 1)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
