-- Prove2me | Theorems.Thm_UnderstandingML_rip_exact_recovery
-- name    : UnderstandingML.rip_exact_recovery
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:24:36.780837+00:00
-- url     : https://prove2.me/theorems/7b03424d-2054-48c9-9159-5dc4715c23dd
-- title:
--   Theorem 23.6: for ε < 1 and W (ε,2s)-RIP, every ‖·‖₀-minimizer v with Wv = Wx equals x when ‖x‖₀ ≤ s
-- statement:
--   **Theorem 23.6.** Let $\epsilon < 1$ and let $W$ be an $(\epsilon, 2s)$-RIP matrix. Let $x$ be a vector s.t. $\|x\|_0 \le s$, let $y = Wx$ be the compression of $x$, and let $\tilde x \in \operatorname{argmin}_{v : Wv = y}\|v\|_0$ be a reconstructed vector. Then, $\tilde x = x$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §23.3 pp. 331-332, Theorem 23.6 with its proof

import Definitions.Def_UnderstandingML_DimReduction

open MeasureTheory ProbabilityTheory

namespace UnderstandingML

/-- **Theorem 23.6** (p. 331). Let `ε < 1` and let `W` be an `(ε, 2s)`-RIP matrix. Let `x` be a
vector s.t. `‖x‖₀ ≤ s`, let `y = Wx` be the compression of `x`, and let
`x̃ ∈ argmin_{v : Wv = y} ‖v‖₀` be a reconstructed vector. Then `x̃ = x`. -/
theorem rip_exact_recovery {n d s : ℕ} (ε : ℝ) (hε : ε < 1) (W : Matrix (Fin n) (Fin d) ℝ)
    (hW : IsRIP ε (2 * s) W) (x xt : Fin d → ℝ) (hx : l0Norm x ≤ s)
    (hy : W.mulVec xt = W.mulVec x) (hmin : ∀ v, W.mulVec v = W.mulVec x → l0Norm xt ≤ l0Norm v) :
    xt = x := by sorry

end UnderstandingML
