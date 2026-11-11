-- Prove2me | Theorems.Thm_QVolKLS_lemma_3_5
-- name    : QVolKLS.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:38:29.507216+00:00
-- url     : https://prove2.me/theorems/d26140a4-cdec-4d64-9df7-afbce20a114e
-- title:
--   Lemma 3.5 — error of a coherently selected reflection: $\xi+2\sqrt\iota$
-- statement:
--   Let $R$ be a unitary on $SA$ (the intended qsample reflection, possibly controlled by qubits in $A$), $E$ fresh implementation workspace, $|\Psi\rangle_{SA}$ a state, and
--   $$
--   |b\rangle_B=\sum_z\sqrt{p_z}\,|z\rangle_B,\qquad p_z\ge0,\qquad \sum_zp_z=1,
--   $$
--   a state of the control register $B$. For each label $z$ let $\tilde R_z$ be a unitary on $ESA$ and $\tilde R_B=\sum_z|z\rangle\langle z|_B\otimes\tilde R_z$. Let $\xi\ge0$, $0\le\iota\le1$, and suppose a set $G$ of good labels satisfies
--   $$
--   \sum_{z\notin G}p_z\le\iota,\qquad \big\|(\tilde R_z-I_E\otimes R)(|0\rangle_E\otimes|\Psi\rangle_{SA})\big\|\le\xi\quad(z\in G).\tag{18}
--   $$
--   Then
--   $$
--   \big\|(\tilde R_B-I_B\otimes I_E\otimes R)(|b\rangle_B\otimes|0\rangle_E\otimes|\Psi\rangle_{SA})\big\|\le\xi+2\sqrt\iota,\tag{19}
--   $$
--   and the same bound holds for the trace distance of the two output states after discarding $E$.
--
--   This charges a reflection controlled by a covariance block for the probability that the block is a bad estimate.
--
--   **Formalization Note** Finite registers; $|0\rangle_E$ is a fixed basis vector of $E$; reduced states on $B\otimes SA$.
--
--   Differences from the source:
--   - generalization: R the intended qsample reflection on SA, possibly controlled by qubits in A → R any unitary on SA; reason: the proof uses only unitarity of R; specializes to qsample reflections
--   - encoding: registers B, E, SA and |0⟩_E → finite index types β, ε, σ and a fixed basis label e₀ of E; reason: all quantum circuits act on finite registers (p.21)
--   - encoding: the same bound in trace distance after discarding workspace → traceDist of the reduced density matrices on B × SA (traceOutMid); reason: discarding E is the partial trace
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Lemma 3.5, p.28

import Definitions.Def_QVolKLS_fourthMomentNorm

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Lemma 3.5 (Error of a coherently
selected reflection)**, p.28. Let `R` be a unitary on `SA` (the intended reflection), `E` fresh
workspace, `|Ψ⟩_SA` a state and `|b⟩_B = Σ_z √p_z |z⟩_B` a control state (`p_z ≥ 0`, `Σ p_z = 1`). Let
`R̃_z` be unitaries on `ESA` and `R̃_B = Σ_z |z⟩⟨z|_B ⊗ R̃_z`. Let `ξ ≥ 0`, `0 ≤ ι ≤ 1`, and let a set `G`
of good labels satisfy `Σ_{z∉G} p_z ≤ ι` and `‖(R̃_z − I_E ⊗ R)(|0⟩_E ⊗ |Ψ⟩_SA)‖ ≤ ξ` for `z ∈ G`
(18). Then `‖(R̃_B − I_B ⊗ I_E ⊗ R)(|b⟩_B ⊗ |0⟩_E ⊗ |Ψ⟩_SA)‖ ≤ ξ + 2√ι` (19), and the same bound holds
for the trace distance of the two output states after discarding `E`.

**Formalization Note.** Registers are finite: `B`, `E`, `SA` have basis index types `β`, `ε`, `σ`, and
`|0⟩_E` is the basis vector of a fixed label `e₀`. The joint register is `B × E × SA`. `R` is any
unitary on `SA` (the proof uses only unitarity; for the paper's `R`, a qsample reflection possibly
controlled by qubits in `A`, this is the printed lemma). The trace-distance clause compares the
reduced density matrices on `B × SA` (`traceOutMid`). -/
theorem lemma_3_5 {β ε σ : Type*} [Fintype β] [DecidableEq β] [Fintype ε] [DecidableEq ε]
    [Fintype σ] [DecidableEq σ] (e0 : ε) (R : Matrix σ σ ℂ)
    (hR : R ∈ Matrix.unitaryGroup σ ℂ) (Rt : β → Matrix (ε × σ) (ε × σ) ℂ)
    (hRt : ∀ z, Rt z ∈ Matrix.unitaryGroup (ε × σ) ℂ) (Ψ : σ → ℂ) (hΨ : jointNorm Ψ = 1)
    (p : β → ℝ) (hp : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1) (G : Finset β) (ξ ι : ℝ)
    (hξ : 0 ≤ ξ) (hι0 : 0 ≤ ι) (hι1 : ι ≤ 1) (hbad : ∑ z ∈ Gᶜ, p z ≤ ι)
    (hgood : ∀ z ∈ G,
      jointNorm (fun q : ε × σ =>
        (∑ q' : ε × σ, Rt z q q' * (if q'.1 = e0 then Ψ q'.2 else 0)) -
          (if q.1 = e0 then ∑ x', R q.2 x' * Ψ x' else 0)) ≤ ξ) :
    jointNorm (fun q : β × ε × σ =>
        (∑ q' : ε × σ, Rt q.1 q.2 q' *
            (((Real.sqrt (p q.1) : ℝ) : ℂ) * (if q'.1 = e0 then Ψ q'.2 else 0))) -
          ((Real.sqrt (p q.1) : ℝ) : ℂ) * (if q.2.1 = e0 then ∑ x', R q.2.2 x' * Ψ x' else 0))
      ≤ ξ + 2 * Real.sqrt ι ∧
    traceDist
        (traceOutMid (fun q : β × ε × σ => ∑ q' : ε × σ, Rt q.1 q.2 q' *
            (((Real.sqrt (p q.1) : ℝ) : ℂ) * (if q'.1 = e0 then Ψ q'.2 else 0))))
        (traceOutMid (fun q : β × ε × σ =>
            ((Real.sqrt (p q.1) : ℝ) : ℂ) * (if q.2.1 = e0 then ∑ x', R q.2.2 x' * Ψ x' else 0)))
      ≤ ξ + 2 * Real.sqrt ι := by sorry

end QVolKLS
