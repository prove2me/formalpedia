-- Prove2me | Theorems.Thm_PolyakJuditsky_Averaging_lemma1_phi_bounds
-- name    : PolyakJuditsky.Averaging.lemma1_phi_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:38:45.063372+00:00
-- url     : https://prove2.me/theorems/8a31e861-6fc6-4b81-ae43-1ac1aa78372c
-- title:
--   Lemma 1 — $\|\varphi_j^t\|\le K$ and $\frac1t\sum_{j<t}\|\varphi_j^t\|\to0$
-- statement:
--   Let $A$ be a real $N\times N$ matrix all of whose eigenvalues have positive real part, and let $\gamma_t>0$ for all $t\ge0$ with $\gamma_t\to0$ and $(\gamma_t-\gamma_{t+1})/\gamma_t=o(\gamma_t)$. Define $X_j^j=I$, $X_j^{t+1}=X_j^t-\gamma_tAX_j^t$ ($t\ge j$), $\bar X_j^t=\gamma_j\sum_{i=j}^{t-1}X_j^i$ and $\varphi_j^t=A^{-1}-\bar X_j^t$. Then there is a constant $K<\infty$ such that for all $j$ and $t\ge j$
--   $$\|\varphi_j^t\|\le K,\tag{A2}$$
--   and
--   $$\lim_{t\to\infty}\frac1t\sum_{j=0}^{t-1}\|\varphi_j^t\|=0.\tag{A3'}$$
--
--   The partial sums $\bar X_j^t$ approximate $A^{-1}$ uniformly on average; this is what turns the averaged iterate of a linear recursion into $A^{-1}$ applied to the averaged noise (Lemma 2).
--
--   **Formalization Note** The paper states the lemma under Assumption 2.2, which allows either a constant step (condition (3)) or condition (4). Only condition (4) is included: condition (3) as printed, $0<\gamma<2(\min_i\operatorname{Re}\lambda_i(A))^{-1}$, is false ($A=\operatorname{diag}(1,10)$, $\gamma=1$ gives $I-\gamma A=\operatorname{diag}(0,-9)$), and Theorem 2 uses only (4). (A3) is printed as $\frac1t\sum_j\varphi_j^t\to0$; the statement has the norm inside, which implies the printed form, is what Part 4 of the proof establishes (p. 846), and is what Lemma 2 needs. $\|\cdot\|$ is the operator norm on Euclidean $\mathbb R^N$.
-- source:
--   Polyak, Juditsky, Acceleration of stochastic approximation by averaging, SIAM J. Control Optim. 30 (1992), p. 844, Lemma 1, Eq. (A1)–(A3)

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open Filter Topology

namespace PolyakJuditsky.Averaging

/-- Lemma 1 (p. 844), under condition (4) with `γ_t > 0` for all `t ≥ 0` and `Re λ_i(A) > 0`:
there is `K < ∞` with `‖φ_j^t‖ ≤ K` for all `j` and `t ≥ j` (A2), and
`(1/t) ∑_{j=0}^{t-1} ‖φ_j^t‖ → 0` ((A3) with the norm inside, the form its proof establishes). -/
theorem lemma1_phi_bounds {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ)
    (hA : EigenRePos A) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ) :
    ∃ K : ℝ, (∀ j t, j ≤ t → matNorm (lemPhi A γ j t) ≤ K) ∧
      Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * ∑ j ∈ Finset.range t, matNorm (lemPhi A γ j t))
        atTop (𝓝 0) := by sorry

end PolyakJuditsky.Averaging
