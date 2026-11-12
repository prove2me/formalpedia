-- Prove2me | Theorems.Thm_RLCDiscrepancy_eq_8
-- name    : RLCDiscrepancy.eq_8
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:53:28.500944+00:00
-- url     : https://prove2.me/theorems/0d7770d5-a2bd-4fc4-9fe0-50ce34596926
-- title:
--   Eq. (8) — $\delta_{C,f}$ as a sum over the dual code
-- statement:
--   Let $\psi$ be a nontrivial additive character of $\mathbb F_q$, $C\subseteq\mathbb F_q^n$ a linear code, and $f:\mathbb F_q^n\to\mathbb R$ with $\hat f(0)=q^{-n}\sum_x f(x)=1$. Then
--
--   $$
--   \delta_{C,f}=\frac1{|C|}\sum_{x\in C}f(x)-1=\sum_{y\in C^\perp}\hat f(y)-1=\sum_{y\in C^\perp\setminus\{0\}}\hat f(y).
--   $$
--
--   This expansion is the bridge between the combinatorics of a code and the Fourier spectrum of the test function; it underlies Lemma 4.12 and the nonnegativity $\delta_{C,F_f}\ge0$.
--
--   Differences from the source:
--   - generalization: f normalized, meaning f̂(0) = ∥f∥_1 = 1 → only ∑_x f(x) = q^n (f̂(0) = 1), no sign condition; reason: for real f the source's condition implies this one
--   - generalization: the trace character → any nontrivial additive character ψ (`ψ ≠ 0`); reason: the trace character is nontrivial; for the trivial character the identity fails
--   - encoding: equalities of real numbers → the first equality in ℝ, the two Fourier ones in ℂ via the coercion; reason: f̂ is complex valued; same statement
--   - encoding: F_q and F^n_q → a finite field `F` with q = `Fintype.card F`, and `Fin n → F`; reason: every prime power is the size of a finite field; same instances
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), §4.2, p.30, Eq. (8) (in the proof of Lemma 4.12)

import Mathlib
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_fourier
import Definitions.Def_RLCDiscrepancy_dual

namespace RLCDiscrepancy

/-- **Eq. (8)** (relative deviation as a sum over the dual code). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), §4.2, p.30, Eq. (8), in
the proof of Lemma 4.12: "For any normalized function f : F^n_q → R (meaning f̂(0) = ∥f∥_1 = 1), we
can express its relative deviation over C using the Fourier transform. … we have:
δ_{C,f} = (1/|C|) ∑_{x∈C} f(x) − 1 = ∑_{y∈C^⊥} f̂(y) − 1 = ∑_{y∈C^⊥∖{0}} f̂(y)."

**Formalization Note.** All three equalities are stated, in `ℂ`. C is any linear code. The
hypothesis on `f` is only f̂(0) = 1, i.e. `∑ x, f x = q ^ n` (no sign condition), and ψ is any
nontrivial additive character of `F` (`ψ ≠ 0`), which contains the paper's trace character;
for the trivial character the identity is false. -/
theorem eq_8 {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 0) (C : Submodule F (Fin n → F)) (f : (Fin n → F) → ℝ)
    (hf : ∑ x, f x = (Fintype.card F : ℝ) ^ n) :
    relDev C f = 1 / ((codeFinset C).card : ℝ) * (∑ x ∈ codeFinset C, f x) - 1 ∧
      (relDev C f : ℂ) = (∑ y ∈ codeFinset (dual C), fourier ψ f y) - 1 ∧
      (relDev C f : ℂ) = ∑ y ∈ codeFinset (dual C) \ {0}, fourier ψ f y := by sorry

end RLCDiscrepancy
