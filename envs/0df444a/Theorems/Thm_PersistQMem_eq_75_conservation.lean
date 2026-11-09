-- Prove2me | Theorems.Thm_PersistQMem_eq_75_conservation
-- name    : PersistQMem.eq_75_conservation
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:35:12.186555+00:00
-- url     : https://prove2.me/theorems/9a818886-04af-4feb-9b23-7cd8c3c32263
-- title:
--   §6.6, (75) — conservation of probability $\int\operatorname{Tr}\omega^\rho_t\,d\nu_t=1$
-- statement:
--   For every persistent-memory receiver (measurable records, memory $\mathbb C^K$, Kraus-density instruments), every density matrix $\rho$ of the source and every round $t$, the trace of the branch state is integrable against the reference measure $\nu_t$ and
--   $$\int\operatorname{Tr}\omega^\rho_t(h)\,d\nu_t(h)=1 .$$
--   The paper's $A_{t,h}$ is the case $\rho=\tau$ and $B_{\lambda,t,h}$ the case $\rho=\rho_\lambda$:
--   $$\int\operatorname{Tr}A_{t,h}\,d\nu_t(h)=\int\operatorname{Tr}B_{\lambda,t,h}\,d\nu_t(h)=1.\tag{75}$$
--
--   It also certifies that $\Pr_\rho(E)$ in Theorem 2.2 is an integral of an integrable function.
--
--   Differences from the source:
--   - generalization: (75) for ρ = τ (A_{t,h}) and ρ = ρ_λ (B_{λ,t,h}) → every density matrix ρ; reason: the argument uses only that ρ is a density matrix; ρ = τ and ρ = ρ_λ are instances
--   - encoding: the protocol model → Protocol X L K D with refMeasure (ν_t) and branch (ω^ρ_t); integrability of the trace asserted; reason: see Protocol; the integrability excludes a junk integral
--   - encoding: real traces Tr(·) (drift, ℓ_j, Tr A) → real parts of complex traces; reason: the traces are real for the Hermitian and positive operators involved
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §6.6, (75), p.28 (PDF p.31); finite form (59), p.26 (PDF p.29)

import Mathlib
import Definitions.Def_PersistQMem_Protocol

open scoped Matrix ComplexOrder
open MeasureTheory

namespace PersistQMem

/-- **§6.6, (75), p.28: conservation of probability** (Tao, Shen, *Structural Lower Bounds for
Quantum Property Estimation with Persistent Memory*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, §6.6, (75), p.28; finite form (59), p.26). For every persistent-memory receiver,
every density matrix `ρ` of the source and every round `t`, the trace of the branch state is
integrable against the reference measure and `∫ Tr ω^ρ_t(h) dν_t(h) = 1`. The paper's `A_{t,h}` is
`ρ = τ` and `B_{λ,t,h}` is `ρ = ρ_λ`. -/
theorem eq_75_conservation {X : Type} [MeasurableSpace X] {L : Type} [Fintype L] {K D : ℕ}
    (P : Protocol X L K D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : WildeQIT.IsDensityOperator ρ)
    (t : ℕ) :
    Integrable (fun h => (branch P ρ t h).trace.re) (refMeasure P t) ∧
    ∫ h, (branch P ρ t h).trace.re ∂(refMeasure P t) = 1 := by sorry

end PersistQMem
