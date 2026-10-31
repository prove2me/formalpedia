-- Prove2me | Theorems.Thm_RobustToDynamics_step3_shrinkage_factor
-- name    : RobustToDynamics.step3_shrinkage_factor
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:36.531768+00:00
-- url     : https://prove2.me/theorems/5f61d5ba-63e1-42fe-8a0c-f9ab0a8cdf3b
-- title:
--   Step 3, (2.17) — $M_{ii}\ge1$, $\gamma\in[0,1)$ and $G^TMG\preceq\gamma M$
-- statement:
--   Let $G$ and $M$ be real $n\times n$ matrices with $G^TMG-M=-I$ and $M\succ0$, and put
--   $$
--   \gamma=1-\frac{1}{\max_{i}\{M_{ii}+\sum_{j\neq i}|M_{ij}|\}}. \tag{2.17}
--   $$
--   Then $M_{ii}\ge1$ for every $i$, $0\le\gamma<1$, and
--   $$
--   G^TMG\preceq\gamma M,
--   $$
--   that is, $\gamma M-G^TMG$ is positive semidefinite.
--
--   So one step of the dynamics maps $E(\alpha)$ into $E(\gamma\alpha)$.
--
--   **Formalization Note** For $n=0$ the maximum is $1$ by convention and $\gamma=0$.
--
--   Differences from the source:
--   - encoding: A ⪯ B → (B − A).PosSemidef; reason: the Loewner order
--   - generalization: M the Lyapunov solution for G with ρ(G) < 1 → any M ≻ 0 with GᵀMG − M = −I; reason: under ρ(G) < 1 the Lyapunov solution satisfies both hypotheses (Step 1)
--   - generalization: rational data → real data; reason: the statement for real matrices specializes to rational ones by casting
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 3, display (2.17), pp.15–16

import Mathlib
import Definitions.Def_RobustToDynamics_gamma

open Matrix

namespace RobustToDynamics

/-- **Step 3, (2.17): the shrinkage factor `γ ∈ [0, 1)` with `GᵀMG ⪯ γM`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 3, display (2.17), pp.15–16: "the number γ = 1 − 1 / max_{i}{Mii + ∑_{j≠i} |Mi,j|} satisfies
GT MG ⪯ γM", and p.16: "as M ≻ 0, and hence GT MG ⪰ 0, we have M − I = GT MG ⪰ 0. This implies
that Mii ≥ 1 for all i ∈ {1, . . . , n} and therefore γ is indeed a number in [0, 1)."

Let `M ≻ 0` solve `GᵀMG − M = −I`. Then `Mᵢᵢ ≥ 1` for every `i`, `0 ≤ γ < 1`, and `γM − GᵀMG` is
positive semidefinite.

**Formalization Note.** `γ` is `gamma M`; `A ⪯ B` is `(B − A).PosSemidef`. For `n = 0` the
maximum over the empty index set is `1` by convention, so `γ = 0`. -/
theorem step3_shrinkage_factor {n : ℕ} (G M : Matrix (Fin n) (Fin n) ℝ)
    (hL : Gᵀ * M * G - M = -1) (hM : M.PosDef) :
    (∀ i, 1 ≤ M i i) ∧ 0 ≤ gamma M ∧ gamma M < 1 ∧
      (gamma M • M - Gᵀ * M * G).PosSemidef := by sorry

end RobustToDynamics
