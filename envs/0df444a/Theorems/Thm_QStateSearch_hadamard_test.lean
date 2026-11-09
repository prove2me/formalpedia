-- Prove2me | Theorems.Thm_QStateSearch_hadamard_test
-- name    : QStateSearch.hadamard_test
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:58.516254+00:00
-- url     : https://prove2.me/theorems/d784b30d-e869-4043-983a-9b12e774c004
-- title:
--   Proof of Theorem 5 — Hadamard test accepts with probability $\|(\langle\psi|\otimes I)\phi\|^2$ under $R_\psi$, $0$ under $I$
-- statement:
--   Let $\phi$ be a vector of the oracle-input register $\mathbb C^D$ and a workspace $W$ (the witness). Prepare a control qubit in $|+\rangle$, apply the controlled oracle, apply a Hadamard gate $H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ to the control, and accept exactly when the outcome is $1$. Then
--
--   1. if the oracle is $R_\psi$ with $\psi$ a unit vector, the acceptance probability is $\sum_w|\sum_i\overline{\psi_i}\phi(i,w)|^2=\|(\langle\psi|\otimes I)\phi\|^2$;
--   2. if the oracle is $I$, the acceptance probability is $0$.
--
--   In particular the witness $\psi$ is accepted with probability one, every witness orthogonal to $\psi$ is rejected with probability one, and under $I$ every witness is rejected. This is the UniqueQMA verifier of Theorem 5; appended to any verifier it converts output fidelity into distinguishing advantage at the cost of one query.
--
--   Differences from the source:
--   - generalization: an $n$-qubit witness $|\phi\rangle$, $U_n\in\{R_{\psi_n},I\}$, and the three printed cases → any vector $\phi$ on $[D]\times W$, any $D$, and the exact acceptance probability under $R_\psi$ and $I$; reason: the three cases follow: $\phi=\psi$ gives $1$, $\phi\perp\psi$ gives $0$, $I$ gives $0$
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), proof of Theorem 5, first paragraph, p.15

import Mathlib
import Definitions.Def_QStateSearch_refl
import Definitions.Def_QStateSearch_ctrlQuery
open Matrix
open scoped Kronecker

namespace QStateSearch

/-- **Proof of Theorem 5, Hadamard test.** The verifier receives a witness `φ`, prepares a
control qubit in `|+⟩`, applies the controlled oracle, applies a Hadamard gate to the control and
accepts exactly when the outcome is `1`. With oracle `R_ψ` (`ψ` a unit vector) it accepts with
probability `‖(⟨ψ| ⊗ I) φ‖²`; with oracle `I` it accepts with probability `0`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), proof of Theorem 5, first paragraph, p.15.

**Formalization Note.** The witness is any vector `φ` of the oracle-input register and a
workspace `W`, so the formula covers the paper's three cases: the witness `ψ` is accepted with
probability one, witnesses orthogonal to `ψ` are rejected, and under `I` every witness is rejected.
`H = (1/√2)[[1, 1], [1, −1]] ⊗ I` acts on the control; the start vector is `|0⟩ ⊗ φ`, so `H` prepares
the control in `|+⟩`. The acceptance probability is the squared norm of the control-`1` part. -/
theorem hadamard_test {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (φ : Fin D × W → ℂ) :
    let H : Matrix (Reg D W) (Reg D W) ℂ :=
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • !![(1 : ℂ), 1; 1, -1]) ⊗ₖ
        (1 : Matrix (Fin D × W) (Fin D × W) ℂ)
    let v₀ : Reg D W → ℂ := fun x => if x.1 = 0 then φ x.2 else 0
    let accProb : Matrix (Fin D) (Fin D) ℂ → ℝ := fun O =>
      ∑ y : Fin D × W, ‖(H *ᵥ (ctrlQuery O *ᵥ (H *ᵥ v₀))) (1, y)‖ ^ 2
    (∀ ψ : EuclideanSpace ℂ (Fin D), ‖ψ‖ = 1 →
      accProb (refl ψ) = ∑ w, ‖∑ i, star (ψ i) * φ (i, w)‖ ^ 2) ∧
    accProb 1 = 0 := by sorry

end QStateSearch
