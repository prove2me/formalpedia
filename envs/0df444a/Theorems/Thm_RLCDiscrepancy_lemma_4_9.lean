-- Prove2me | Theorems.Thm_RLCDiscrepancy_lemma_4_9
-- name    : RLCDiscrepancy.lemma_4_9
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:53:26.983212+00:00
-- url     : https://prove2.me/theorems/5914be6f-499a-4fce-98b0-dacbcf7374de
-- title:
--   Lemma 4.9 — Fourier transform of $F_f$ is $|\hat f|^2$
-- statement:
--   Let $f:\mathbb F_q^n\to\mathbb R$ and let $\psi$ be any additive character of $\mathbb F_q$, with $\hat f$ the Fourier transform with respect to $\psi$. Then for every $y\in\mathbb F_q^n$,
--
--   $$
--   \widehat{F_f}(y)=\big|\hat f(y)\big|^2 .
--   $$
--
--   In particular the Fourier coefficients of the self-convolution are nonnegative reals, which makes $\delta_{C,F_f}\ge0$ for every code $C$ and turns the variance of the one-step change of $\delta_{C,f}$ into a deviation of $F_f$ (Lemma 4.12).
--
--   Differences from the source:
--   - generalization: f : F^n_q → R≥0 normalized → any real-valued f; reason: the identity holds for every real f; normalized nonnegative f are instances
--   - generalization: the trace character χ_y(x) = exp(2πi tr(⟨x,y⟩)/p) → any additive character ψ of F; reason: the trace character is one such ψ
--   - encoding: F_q and F^n_q → a finite field `F` with q = `Fintype.card F`, and `Fin n → F`; reason: every prime power is the size of a finite field; same instances
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.9, p.29

import Mathlib
import Definitions.Def_RLCDiscrepancy_selfConv
import Definitions.Def_RLCDiscrepancy_fourier

namespace RLCDiscrepancy

/-- **Lemma 4.9** (Fourier transform of F_f). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.9, p.29: "Let f : F^n_q → R≥0 be a
normalized function. Then, F̂_f(y) = |f̂(y)|² for all y ∈ F^n_q."

**Formalization Note.** Stated for every real-valued `f` (no nonnegativity or normalization)
and every additive character `ψ` of `F`, which contains the paper's trace character; the
Fourier transform is the paper's, with no conjugate. -/
theorem lemma_4_9 {F : Type*} [Field F] [Fintype F] {n : ℕ} (ψ : AddChar F ℂ)
    (f : (Fin n → F) → ℝ) (y : Fin n → F) :
    fourier ψ (selfConv f) y = ((‖fourier ψ f y‖ ^ 2 : ℝ) : ℂ) := by sorry

end RLCDiscrepancy
