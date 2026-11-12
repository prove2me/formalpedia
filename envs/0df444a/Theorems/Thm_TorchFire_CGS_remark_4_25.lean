-- Prove2me | Theorems.Thm_TorchFire_CGS_remark_4_25
-- name    : TorchFire.CGS.remark_4_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:44:41.17304+00:00
-- url     : https://prove2.me/theorems/48690c08-81be-464b-9359-97eed66da497
-- title:
--   Remark 4.25 — coherent tag correctness $\mathbb E[\sup_\psi\Vert(I-\Pi)\mathrm{Fire.Tag}(|K\rangle|\psi\rangle|0\rangle)\Vert^2]\le\mathrm{negl}(\mu)$
-- statement:
--   For each oracle and setup sample of Remark 4.24, let $\Pi$ be the diagonal projector on $(Z,Y,R_0,R_1)$ onto the basis values with $\mathrm{Fire.Check}(z,(y,\tau_0,\tau_1))=1$, acting as the identity on all other registers. For every finite-dimensional register $E$, extend $\mathrm{Fire.Tag}^O$ (95) and $\Pi$ by the identity on $E$. Then
--   $$\mathbb E\Big[\sup_{\Vert|\psi\rangle_{ZE}\Vert=1}\big\Vert(I-\Pi)\,\mathrm{Fire.Tag}^O\big(|K\rangle\otimes|\psi\rangle_{ZE}\otimes|0\rangle\big)\big\Vert^2\Big]\le\mathrm{negl}(\mu)\quad(30),$$
--   where $|0\rangle$ comprises the response and signing workspace registers and the expectation is over oracle generation and setup. One negligible function bounds every $E$.
--
--   Adapted from [ÇGS26, §9.4], without proof in the source. It is the tag error $e_{\mathrm{tag}}$ of torch-fire's affine queries.
--
--   Differences from the source:
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - encoding: any polynomially bounded ℓ ≥ r + k + 3 (21) → ℓ = r + k + 3; reason: the least allowed value; nothing depends on the choice
--   - encoding: OSS.Sign with intermediate measurements; U^O_{y,b} obtained from it by Fact 3.1 (Remark 4.12) → the deferred-measurement signing circuit written gate by gate; the zero state of Σ is |⊥⟩; reason: paper.md decisions 6 and 16
--   - generalization: for every finite-dimensional E, the expectation is ≤ negl(µ) → one negligible ν bounds the expectation for every nonempty finite E; reason: the supremum of the quadratic form ⟨ψ|(M_Z ⊗ I_E)|ψ⟩ does not depend on E, so the two readings are equivalent
--   - encoding: a finite-dimensional register E → a nonempty finite type; reason: a zero-dimensional register has no unit vectors
--   - encoding: expectation over oracle generation and setup → average over the oracle sample; reason: neither Π nor |K⟩ depends on the setup label
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Remark 4.25, (30), p.29 (adapted from [ÇGS26, §9.4])

import Mathlib
import Definitions.Def_TorchFire_CGS_tagErr
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS PPADSIS.SubexpSIS

namespace TorchFire.CGS

/-- **Remark 4.25** (coherent tag correctness, adapted from [ÇGS26, §9.4]), (30), p.29 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). Let `Π`
be the diagonal projector on `(Z, Y, R_0, R_1)` onto the basis values with
`Fire.Check(z, (y, τ_0, τ_1)) = 1`, the identity on all other registers. For every finite-dimensional
register `E`, with `Fire.Tag^O` (95) and `Π` extended by the identity on `E`,
`E[sup_{‖|ψ⟩_{ZE}‖=1} ‖(I − Π) Fire.Tag^O(|K⟩ ⊗ |ψ⟩_{ZE} ⊗ |0⟩)‖²] ≤ negl(µ)`, the expectation over oracle
generation (and setup, on which neither side depends). One negligible function serves every `E`. The
source cites [ÇGS26] and gives no proof. -/
theorem remark_4_25 :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E] (mu : ℕ),
        avg (Sample mu) (fun ω => tagErr ω E) ≤ ν mu := by sorry

end TorchFire.CGS
