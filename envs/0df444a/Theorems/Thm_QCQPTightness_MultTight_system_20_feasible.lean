-- Prove2me | Theorems.Thm_QCQPTightness_MultTight_system_20_feasible
-- name    : QCQPTightness.MultTight.system_20_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:38.292302+00:00
-- url     : https://prove2.me/theorems/4eb21f2f-5e78-4004-a43d-4271fe4a67e5
-- title:
--   App. B, proof of Theorem 8, p. 35 — if k ≥ m + 1, the system (20) ⟨A_i x̂ + b_i, y ⊗ z⟩ = 0, y ∈ 𝐒^{k−1} is feasible
-- statement:
--   Let $N = kn$ and $k\ge m+1$. For any $\hat x\in\mathbb R^N$ and $z\in\mathbb R^n$ there is $y\in\mathbb R^k$ with
--
--   $$\langle A_i\hat x+b_i,\ y\otimes z\rangle = 0\quad\forall i\in[\![m]\!],\qquad y\in\mathbf S^{k-1},$$
--
--   where $\mathbf S^{k-1}$ is the Euclidean unit sphere of $\mathbb R^k$. (This is system (20) of the paper.)
--
--   The vector $y$ gives a direction $y\otimes z$ along which every constraint's linear part vanishes; in the proof of Theorem 8 it is used to move $\hat x$ to $\hat x\pm y\otimes z$ without leaving the feasible set of (19).
--
--   **Formalization Note** $y\in\mathbf S^{k-1}$ is $y\cdot y = 1$. No representation hypothesis on the $A_i$ is needed; the statement holds for any matrices $A_i$ and vectors $b_i$.
-- source:
--   arXiv:1911.09195v3, App. B, proof of Theorem 8, p. 35, display (20)

import Mathlib
import Definitions.Def_QCQPTightness_MultTight_QCQP
import Definitions.Def_QCQPTightness_MultTight_Mult
import Definitions.Def_QCQPTightness_MultTight_Kron

namespace QCQPTightness.MultTight

open QCQP Matrix

/-- App. B, proof of Theorem 8 (arXiv:1911.09195v3, p. 35): if `k ≥ m + 1`, the system (20)
`⟨A_i x̂ + b_i, y ⊗ z⟩ = 0` (`i ∈ ⟦m⟧`), `y ∈ 𝐒^{k−1}` has a solution `y ∈ ℝ^k`. -/
theorem system_20_feasible {N m : ℕ} (P : QCQP N m) {k n : ℕ} (h : k * n = N)
    (hkm : m + 1 ≤ k) (x : Fin N → ℝ) (z : Fin n → ℝ) :
    ∃ y : Fin k → ℝ, y ⬝ᵥ y = 1 ∧
      ∀ i, (P.A i *ᵥ x + P.b i) ⬝ᵥ kronVec h y z = 0 := by sorry

end QCQPTightness.MultTight
