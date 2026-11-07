-- Prove2me | Theorems.Thm_QLocalCert_lemma_8
-- name    : QLocalCert.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:19.348687+00:00
-- url     : https://prove2.me/theorems/689107a8-80dd-4a9e-872e-23bca31e8139
-- title:
--   Lemma 8 — SWAP test: $D(\rho_A,\rho_B)\le2\kappa$ and $\kappa\le\sqrt{\alpha(1-\alpha)}\le\sqrt\alpha$
-- statement:
--   Let $\rho$ be a density operator on two registers $\mathsf A,\mathsf B$ of the same dimension, let $\Pi_\pm=(I\pm S)/2$ be the projectors onto the symmetric and antisymmetric subspaces, and set
--   $$
--   \alpha=\operatorname{tr}(\Pi_-\rho),\qquad \kappa=\|\Pi_+\rho\Pi_-\|_1 ,
--   $$
--   the rejection probability of the SWAP test and the trace norm of the off-diagonal block. With $\rho_{\mathsf A},\rho_{\mathsf B}$ the reduced states and $D(\sigma,\tau)=\tfrac12\|\sigma-\tau\|_1$ the trace distance,
--   1. $D(\rho_{\mathsf A},\rho_{\mathsf B})\le2\kappa$;
--   2. $\kappa\le\sqrt{\alpha(1-\alpha)}\le\sqrt\alpha$.
--
--   This converts a small rejection probability of the SWAP test into closeness of the two marginals, which is what makes the chain of tests in Protocol 1 telescope along the path.
--
--   **Formalization Note** $D(\sigma,\tau)$ is `WildeQIT.traceDist σ τ / 2` (the published `traceDist` has no factor $\tfrac12$); $\alpha$ is the real part of the trace.
--
--   Differences from the source:
--   - encoding: registers A and B with dim A = dim B → one finite index type d for both registers; reason: equal dimensions identify the two registers
--   - encoding: D(ρ_A, ρ_B) → WildeQIT.traceDist (ptrB ρ) (ptrA ρ) / 2; reason: the published traceDist is ‖·‖₁ without the factor ½
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Lemma 8, p.18

import Mathlib
import Definitions.Def_QLocalCert_swapOp
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_traceDist

open Matrix
open scoped ComplexOrder
set_option autoImplicit false

namespace QLocalCert

/-- **Lemma 8** (p.18). "Let ρ be a bipartite state on two registers A and B with dim A = dim B,
let Π± be a projector onto the symmetric and antisymmetric subspaces, and set the rejection
probability of the swap test α := tr(Π−ρ) and κ := ‖Π+ρΠ−‖₁. Then 1. D(ρ_A, ρ_B) ≤ 2κ
2. κ ≤ √(α(1 − α)) ≤ √α where ρ_A, ρ_B are the reduced states on registers A and B and D is the
trace distance."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Lemma 8, p.18.

**Formalization Note.** Both registers are indexed by the same finite type `d` (`dim A = dim B`).
The paper's trace distance is `D(ρ, σ) = ½‖ρ − σ‖₁` (p.14), i.e. `WildeQIT.traceDist ρ σ / 2`
(`traceDist` has no factor ½). `ρ_A = ptrB ρ`, `ρ_B = ptrA ρ`. `α` is the real part of the trace
(the trace is real for a density operator). -/
theorem lemma_8 {d : Type} [Fintype d] [DecidableEq d] (ρ : Matrix (d × d) (d × d) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) :
    let α : ℝ := (trace (antisymProj d * ρ)).re
    let κ : ℝ := WildeQIT.traceNorm (symProj d * ρ * antisymProj d)
    WildeQIT.traceDist (ptrB ρ) (ptrA ρ) / 2 ≤ 2 * κ ∧
      κ ≤ Real.sqrt (α * (1 - α)) ∧ Real.sqrt (α * (1 - α)) ≤ Real.sqrt α := by sorry

end QLocalCert
