-- Prove2me | Theorems.Thm_SharpPauliEntanglement_Exact_exact_universal_separability_threshold
-- name    : SharpPauliEntanglement.Exact.exact_universal_separability_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:55:26.855677+00:00
-- url     : https://prove2.me/theorems/d9d3add1-64e3-4d79-884c-dc6950cfc61a
-- title:
--   Theorem 1.1 — Universal Pauli-product decomposition at and below zΔ, and finite commuting entangled witnesses above it
-- statement:
--   Fix an integer $\Delta\ge2$, a coefficient magnitude scale $J\ge0$, and an inverse temperature $\beta\ge0$. Put $b=\Delta-1$, $x_\Delta=\sqrt{b^2+1}-b$, and
--
--   $$t_\Delta=x_\Delta\left(\frac{1-x_\Delta}{1+x_\Delta}\right)^b,\qquad z_\Delta=\operatorname{arctanh}(t_\Delta).$$
--
--   For every finite-qubit Hamiltonian $H=\sum_iJ_iP_i$ with real coefficients satisfying $|J_i|\le J$ and specified term-overlap graph of degree at most $\Delta$,
--
--   $$\beta J\le z_\Delta\quad\Longrightarrow\quad\rho_\beta(H)\text{ is a convex combination of product Pauli eigenstates}.$$
--
--   Conversely,
--
--   $$\beta J>z_\Delta\quad\Longrightarrow\quad\exists\text{ a finite commuting Pauli Hamiltonian with }|J_i|=J,\ \deg G\le\Delta,\ \rho_\beta(H)\text{ not fully separable}.$$
--
--   The latter negates separability among arbitrary normalized single-qubit pure projectors, not just membership in the Pauli-product hull. Both statements are at the same prescribed $\beta,J,\Delta$. The equality case belongs to the universal guarantee; above it there are entangled witnesses, with no assertion that every Hamiltonian is entangled. The upper statement includes $\beta=0$, $J=0$, and an empty term set.
--
--   **Formalization Note** Nonidentity Pauli strings and nonzero coefficients follow the source specified-decomposition convention; zero coefficients are discarded. There is no fixed locality bound and no commutation hypothesis in the universal clause. The Gibbs density is the actual normalized matrix exponential.
--
--   Differences from the source:
--   - encoding: arbitrary finite qubit and term labels → computational bitstrings and Fin n, Fin m labels; reason: finite reindexing preserves every matrix, support relation and source instance
--   - encoding: coefficient magnitude bound and beta >= 0 in (1.1), with zero terms discarded in section 2 → an explicit nonnegative scale J, nonnegative beta, nonzero real term coefficients, nonidentity words, and degree <= Delta; reason: these make the source magnitude and decomposition conventions explicit while retaining beta = 0, J = 0 and empty Hamiltonians
--   - encoding: z_Delta defined by the maximum in (1.2) → the equal explicit radical formula of (1.2) and (1.4); reason: the source gives these exact expressions as equal; no approximation or supremum default is used
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), printed/PDF p. 3, Theorem 1.1

import Definitions.Def_SharpPauliEntanglement_Exact_GraphWeights

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Kiani, p. 3, Theorem 1.1, both full-strength clauses at the exact threshold.
The upper clause includes β=0, J=0 and m=0; the lower clause negates arbitrary-pure
full separability rather than only membership in the Pauli-product hull. -/
theorem exact_universal_separability_threshold (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 ≤ β) :
    ((∀ (n m : ℕ) (H : PauliHamiltonian (Fin n) (Fin m)),
      (∀ i, |H.coeff i| ≤ J) → DegreeBound (overlapGraph H) Δ →
      β * J ≤ criticalZ Δ → PauliSeparable (gibbs (hamiltonian H) β)) ∧
    (criticalZ Δ < β * J →
      ∃ (n m : ℕ) (H : PauliHamiltonian (Fin n) (Fin m)),
        (∀ i, |H.coeff i| = J) ∧ DegreeBound (overlapGraph H) Δ ∧
        (∀ i j, Commute (pauliOp (H.term i)) (pauliOp (H.term j))) ∧
        ¬ FullySeparable (gibbs (hamiltonian H) β))) := by sorry

end SharpPauliEntanglement.Exact
