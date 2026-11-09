-- Prove2me | Theorems.Thm_SharpPauliEntanglement_Exact_inclusion_exclusion_pauli_norm
-- name    : SharpPauliEntanglement.Exact.inclusion_exclusion_pauli_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:35.35891+00:00
-- url     : https://prove2.me/theorems/4369a2e6-083e-4b2b-8888-e22bc28c679e
-- title:
--   Lemma 3.5 — ∥Dᵤ∥P,1≤t^|U|wA(U) for every U⊆V at βJ≤zΔ
-- statement:
--   Let $H=\sum_{i\in V}J_iP_i$ have $m\ge1$ nonzero real coefficients, with $|J_i|\le J$, $J\ge0$, and term-overlap degree at most an integer $\Delta\ge2$. Assume $\beta>0$ and $\beta J\le z_\Delta$. Let $A$ be the anticommutation graph and use the original degree-bound parameters $t=t_\Delta$, $\alpha=1+x_\Delta/2$, and $\eta=1/3+x_\Delta/2$. For every $U\subseteq V$, including the empty set,
--
--   $$\|D_U\|_{P,1}\le t^{|U|}w_A(U),\qquad w_A(U)=\prod_{C\in\mathcal C(A[U]),\ |C|\ge2}\eta\alpha^{|C|-1}.$$
--
--   This gives the admissible threshold shifts in (3.19). Anticommutation components need not have disjoint physical supports; the conclusion bounds a norm, not a tensor factorization of separability.
--
--   Differences from the source:
--   - encoding: arbitrary finite qubit and term labels → computational bitstrings and Fin n, Fin m labels; reason: finite reindexing preserves every matrix, support relation and source instance
--   - encoding: positive coefficient magnitude scale and the section standing assumptions → J >= 0, beta > 0, m > 0, coefficient and degree bounds written explicitly; reason: these are precisely the source model and nontrivial regime; nonzero coefficients already force J > 0 here
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), printed/PDF p. 11, Lemma 3.5

import Definitions.Def_SharpPauliEntanglement_Exact_Polymers

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Kiani, p. 11, Lemma 3.5, with the nontrivial §3 regime and §2 degree bound. -/
theorem inclusion_exclusion_pauli_norm {n m : ℕ} (H : PauliHamiltonian (Fin n) (Fin m))
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hm : 0 < m) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (hcoeff : ∀ i, |H.coeff i| ≤ J) (hdegree : DegreeBound (overlapGraph H) Δ)
    (htemp : β * J ≤ criticalZ Δ) (U : Finset (Fin m)) :
    pauliNorm (inclusionExclusion H β U) ≤
      criticalT Δ ^ U.card * redWeight (antiGraph H) Δ U := by sorry

end SharpPauliEntanglement.Exact
