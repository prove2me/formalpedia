-- Prove2me | Theorems.Thm_QSampVerif_lemma_4_3
-- name    : QSampVerif.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:28:49.943278+00:00
-- url     : https://prove2.me/theorems/64d4edae-d31b-416d-baca-6aafe72515a7
-- title:
--   Lemma 4.3 — update correctness of the one-time pad past $\mathrm{CZ}$ (up to global phase)
-- statement:
--   For $x_1,x_2\in\{0,1\}$ and $t_1,t_2\in\{0,\dots,7\}$, let $(x_1',t_1',x_2',t_2')=\mathrm{updateCZ}(x_1,t_1,x_2,t_2)=(x_1,t_1+4x_2,x_2,t_2+4x_1)$. Then, up to a global phase,
--
--   $$(X^{x_1}T^{t_1}\otimes X^{x_2}T^{t_2})\,\mathrm{CZ}=\mathrm{CZ}\,(X^{x_1'}T^{t_1'}\otimes X^{x_2'}T^{t_2'}),\qquad(45)$$
--
--   that is, the two sides differ by a scalar $\omega$ with $|\omega|=1$.
--
--   The lemma lets the verifier update its one-time-pad keys past each homomorphic $\mathrm{CZ}$ of the MBQC protocol.
--
--   **Formalization Note** The paper declares (p.25) that "Operator identities used to commute pads are understood up to global phase". As an exact matrix identity (45) fails at $x_1=x_2=1$, $t_1=t_2=0$: the left side is $(X\otimes X)\mathrm{CZ}$ and the right side is its negative.
--
--   Differences from the source:
--   - reading: (45) as an operator identity → equality up to a global phase: ∃ ω, ‖ω‖ = 1 ∧ LHS = ω • RHS; reason: the paper's convention on p.25; the exact identity fails at x₁ = x₂ = 1, t₁ = t₂ = 0 (LHS = −RHS)
--   - encoding: x ∈ {0, 1}, t ∈ {0, …, 7}; CZ → x ∈ ZMod 2, t ∈ ZMod 8 ("interpreted modulo 2 / modulo 8", p.25); the published controlled pauliZ; reason: same instances
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Lemma 4.3, (45), p.27 (PDF 28); Definition 4.1, (43), p.25 (PDF 26)

import Definitions.Def_QSampVerif_updateCZ

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms
open scoped Matrix Kronecker

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Lemma 4.3 (Update Correctness), (45), p.27 (PDF 28).

For `x₁, x₂ ∈ {0, 1}` and `t₁, t₂ ∈ {0, …, 7}`,
`(X^{x₁} T^{t₁} ⊗ X^{x₂} T^{t₂}) CZ = CZ (X^{x₁'} T^{t₁'} ⊗ X^{x₂'} T^{t₂'})` with
`(x₁', t₁', x₂', t₂') = updateCZ(x₁, t₁, x₂, t₂)`, up to global phase.

**Formalization Note.** The paper declares (p.25): "Operator identities used to commute pads are
understood up to global phase". As an exact matrix identity (45) fails at `x₁ = x₂ = 1`,
`t₁ = t₂ = 0` (the two sides differ by `−1`), so the statement is equality up to a unit scalar.
`CZ` is the published `controlled pauliZ`. -/
theorem lemma_4_3 (x₁ x₂ : ZMod 2) (t₁ t₂ : ZMod 8) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      (padXT x₁ t₁ ⊗ₖ padXT x₂ t₂) * controlled pauliZ =
        ω • (controlled pauliZ *
          (padXT (updateCZ x₁ t₁ x₂ t₂).1 (updateCZ x₁ t₁ x₂ t₂).2.1 ⊗ₖ
            padXT (updateCZ x₁ t₁ x₂ t₂).2.2.1 (updateCZ x₁ t₁ x₂ t₂).2.2.2)) := by sorry

end QSampVerif
