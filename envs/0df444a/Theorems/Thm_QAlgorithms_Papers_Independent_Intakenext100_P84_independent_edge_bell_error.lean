-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P84_independent_edge_bell_error
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P84.independent_edge_bell_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:12:26.369909+00:00
-- url     : https://prove2.me/theorems/fbaab9cb-a192-415a-8c32-191c2ae1104f
-- title:
--   Independent edge Bell products have additive trace-norm error
-- statement:
--   Let $E$ be the finite set of labelled edges. For every $e\in E$, let $m_e\in\mathbb N$ and let $\rho_e$ be a normalized density operator on the two endpoint registers of $m_e$ Bell pairs. Write $\Phi_{m_e}=(|\Phi^+\rangle\langle\Phi^+|)^{\otimes m_e}$, where $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$. Suppose $\varepsilon>0$ and $\|\rho_e-\Phi_{m_e}\|_1\le\varepsilon$ for every edge. Then
--
--   $$
--   \left\|\bigotimes_{e\in E}\rho_e-\bigotimes_{e\in E}\Phi_{m_e}\right\|_1\le |E|\varepsilon.
--   $$
--
--   The norm is the full Schatten $1$-norm. Empty products are the one-dimensional unit state, and zero Bell copies are allowed. This estimate controls the error of the independently prepared Bell-resource network.
--
--   **Formalization Note** The two halves of each Bell product are grouped by endpoint, so its vector is the accepted normalized maximally entangled vector on two $m_e$-qubit registers.
-- source:
--   Aggregating quantum repeaters for the quantum internet, arXiv:1606.00135v1, PDF p. 3, Eq.(4)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P84

open QAlgorithms

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Eq.(4): independent normalized edge outputs, each epsilon-close
in full trace norm to m(e) Bell pairs, have joint error at most |E| epsilon.
`maxEntangled m` is the Bell product with the two endpoint registers grouped
locally; its amplitude is 2^(-m/2). Zero copies give the tensor unit. -/
theorem independent_edge_bell_error {E : Type*} [Fintype E]
    (m : E → ℕ)
    (rho : (e : E) → Matrix (Qubits (m e) × Qubits (m e))
      (Qubits (m e) × Qubits (m e)) ℂ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hrho : ∀ e, IsDensityMatrix (rho e))
    (hedge : ∀ e,
      traceNorm (rho e - pureDensity (maxEntangled (m e))) ≤ epsilon) :
    traceNorm (edgeTensor rho -
      edgeTensor (fun e => pureDensity (maxEntangled (m e)))) ≤
        (Fintype.card E : ℝ) * epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P84

end
