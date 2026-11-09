-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_prop_9
-- name    : TFIMPhaseDiagram.Classical.prop_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:51.594812+00:00
-- url     : https://prove2.me/theorems/3c9dfa3e-9b1e-47b0-86e2-edb8ad879049
-- title:
--   Proposition 9 — Multiplicative Trotter bound for every X-subset
-- statement:
--   Let $J$ be symmetric, $h$ real, $\eta_i\ge0$, $S\subseteq[n]$, and $0<\epsilon<1$. Put $c=2\max_i(\sum_{j\ne i}|J_{ij}|+|h_i|)$. If $M\ge3$ and $M\ge c((c+1)n+2\sum_i|\eta_i|)/\epsilon$, then
--   $$\operatorname{Tr}(X_Se^H)e^{-\epsilon}\le\operatorname{Tr}(X_SQ_M)\le\operatorname{Tr}(X_Se^H)e^{\epsilon}.$$
--   The result supplies multiplicative accuracy for every X-subset, including the empty subset and exact-zero traces.
--
--   Differences from the source:
--   - encoding: ordered real traces → real parts of these real traces on the bitstring basis; reason: For nonnegative fields the two traces are real; the inequalities are unchanged.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.7 = PDF p.7, Proposition 9

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Proposition 9, p.7: the full nonnegative-field multiplicative Trotter bound. -/
theorem prop_9 {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i)
    (S : Finset (Fin n)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (M : ℕ) (hM : 3 ≤ M)
    (hmesh : (M : ℝ) ≥ trotterConstant J h *
      ((trotterConstant J h + 1) * n + 2 * ∑ i, |η i|) / ε) :
  (Matrix.trace (xSubset S * matrixExp (hamiltonian J h η))).re * Real.exp (-ε) ≤
    (Matrix.trace (xSubset S * trotter J h η M)).re ∧
  (Matrix.trace (xSubset S * trotter J h η M)).re ≤
    (Matrix.trace (xSubset S * matrixExp (hamiltonian J h η))).re * Real.exp ε := by sorry
end TFIMPhaseDiagram.Classical
