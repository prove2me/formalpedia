-- Prove2me | Theorems.Thm_QFairEx_theorem_4_7
-- name    : QFairEx.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:25:56.448968+00:00
-- url     : https://prove2.me/theorems/a7d54ed4-8227-49f3-b3c1-9f2272d12bc7
-- title:
--   Theorem 4.7 — two copies of a BB84 state reveal its basis with probability $3/4$
-- statement:
--   For every $\theta,x\in\{0,1\}$, Algorithm 4.6 run on $|\phi\rangle\otimes|\phi\rangle$ with $|\phi\rangle=H^\theta X^x|0\rangle$ outputs $\theta$ with probability exactly $3/4$:
--   $$\operatorname{Re}\operatorname{tr}\bigl(M_\theta\,(|\phi\rangle\langle\phi|\otimes|\phi\rangle\langle\phi|)\bigr)=\tfrac34 .$$
--
--   The reduction uses this on whichever challenge it manages to obtain twice.
--
--   Differences from the source:
--   - encoding: Algorithm 4.6 outputs θ with probability 3/4 → Re tr(clonedPOVM θ · ρ) = 3/4 for ρ = |ϕ⟩⟨ϕ| ⊗ |ϕ⟩⟨ϕ|; reason: the algorithm's output distribution by the Born rule; same instances
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Theorem 4.7, p.22

import Mathlib
import Definitions.Def_QFairEx_SupportedOn
import Definitions.Def_QFairEx_bb84
import Definitions.Def_QFairEx_clonedPOVM

namespace QFairEx

open Matrix

/-- **Theorem 4.7 (two copies reveal the basis with probability 3/4).** Chung, Lee, Raizes,
Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of 2026-11-02, sha256
0099b883…), Theorem 4.7, p.22: "For every θ, x ∈ {0, 1}, Algorithm 4.6 outputs θ with
probability 3/4."

On the input `|ϕ⟩ ⊗ |ϕ⟩`, `|ϕ⟩ = H^θ X^x |0⟩`, the probability `Re tr(clonedPOVM θ · ρ)` that
Algorithm 4.6 answers `θ` is `3/4`. -/
theorem theorem_4_7 (θ x : Bool) :
    (clonedPOVM θ * pureDensity (fun a : Fin 2 × Fin 2 => bb84 θ x a.1 * bb84 θ x a.2)).trace.re =
      3 / 4 := by sorry

end QFairEx
