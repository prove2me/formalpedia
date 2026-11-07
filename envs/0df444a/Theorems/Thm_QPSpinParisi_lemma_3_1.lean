-- Prove2me | Theorems.Thm_QPSpinParisi_lemma_3_1
-- name    : QPSpinParisi.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:39.399621+00:00
-- url     : https://prove2.me/theorems/136c1791-ff7e-45aa-8549-b3b641a8c956
-- title:
--   Lemma 3.1 — Bloch reduction: $E^\star_{n,\mathrm{prod}}=\frac1n\max_sX_n(s)$, and concentration
-- statement:
--   Let $(c_p)$ satisfy the mixture assumption.
--
--   1. The Bloch vector of a unit qubit lies on $S^2$. If $s_i$ is the Bloch vector of $|\phi(i)\rangle$ and $|\phi\rangle=\bigotimes_i|\phi(i)\rangle$, then for all coefficients $\alpha$,
--   $$X_n(s)=\sqrt n\,\langle\phi|H_n|\phi\rangle.\tag{3.1}$$
--   2. Every $s\in(S^2)^n$ arises from some product state.
--   3. Consequently,
--   $$E^\star_{n,\mathrm{prod}}=\frac1n\max_{s\in(S^2)^n}X_n(s),$$
--   and the maximum is attained.
--   4. $E^\star_{n,\mathrm{prod}}$ is integrable, and for every $t>0$,
--   $$\mathbb P\big(|E^\star_{n,\mathrm{prod}}-\mathbb E E^\star_{n,\mathrm{prod}}|>t\big)\le2\exp\Big(-\frac{nt^2}{2\xi(1)}\Big),$$
--   so that $E^\star_{n,\mathrm{prod}}-\mathbb E E^\star_{n,\mathrm{prod}}=o_P(1)$.
--
--   This turns the quantum optimization over product states into a classical maximization over $(S^2)^n$.
--
--   Differences from the source:
--   - reading: $\sum_{p\ge2}$ in (2.1) → the sum over $p$ stops at $p=n$; reason: a $p$-local string needs $p$ distinct sites, and (3.1), (3.5) print $\sum_{p=2}^n$
--   - encoding: increasing tuples $\bar i$ and strings $\bar a$ → subsets $S$ with $|S|\ge2$ and maps $S\to$ `Fin 3`; reason: the same index set
--   - encoding: the complex number $\langle\phi|H_n|\phi\rangle$ → its real part; reason: $H_n$ is Hermitian, so the value is real
--   - encoding: $\xrightarrow{P}$ on a common space → the measure of the deviation event, for each $n$ on its own space; reason: no common space exists across $n$, and convergence in probability only reads these numbers
--   - generalization: $o_P(1)$ in the statement of Lemma 3.1 → also the explicit tail printed in its proof, p.11, and integrability; reason: the source's $o_P(1)$ follows from these
--   - reading: "$\max$" → attainment is stated (`IsGreatest`); reason: the source writes a maximum
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.1, p.10 (PDF p.10); tail bound, p.11 (PDF p.11)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_En
import Definitions.Def_QPSpinParisi_Xn
import Definitions.Def_QPSpinParisi_blochVec
import Definitions.Def_QPSpinParisi_gaussMeas
import Definitions.Def_QPSpinParisi_xiS

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.1, p.10, PDF p.10, with the tail bound on p.11, PDF p.11.

Part (a): the Bloch vector of a unit qubit lies on `S²`, and `X_n(s) = √n ⟨ϕ|H_n|ϕ⟩` for the Bloch vectors `s` of a product state.
Part (b): every `s ∈ (S²)ⁿ` arises from a product state. Part (c): `E⋆_{n,prod} = (1/n) max_s X_n(s)`, with the maximum attained.
Part (d): the Gaussian concentration tail, and `E⋆_{n,prod} - E E⋆_{n,prod} = o_P(1)`.

**Formalization Note** The spaces change with `n`, so convergence in probability is written with the measure of the deviation event. -/
theorem lemma_3_1 (c : ℕ → ℝ) (hc : MixHyp c) :
    (∀ f : Bool → ℂ, IsUnitQubit f → ‖blochVec f‖ = 1) ∧
    (∀ (n : ℕ) (α : Idx n → ℝ) (φ : Fin n → Bool → ℂ), (∀ j, IsUnitQubit (φ j)) →
      ∀ s : RGGDetect.Config n 3, (∀ j, (s j : E3) = blochVec (φ j)) →
        Xn c n α s = Real.sqrt n * energy (ham c n α) (prodKet φ)) ∧
    (∀ (n : ℕ) (s : RGGDetect.Config n 3), ∃ φ : Fin n → Bool → ℂ,
      (∀ j, IsUnitQubit (φ j)) ∧ ∀ j, blochVec (φ j) = (s j : E3)) ∧
    (∀ (n : ℕ) (α : Idx n → ℝ), IsGreatest (range (Xn c n α)) ((n : ℝ) * En c n α)) ∧
    (∀ n : ℕ, Integrable (En c n) (gaussMeas n)) ∧
    (∀ (n : ℕ) (t : ℝ), 0 < t →
      gaussMeas n {α | t < |En c n α - ∫ a, En c n a ∂(gaussMeas n)|} ≤
        ENNReal.ofReal (2 * Real.exp (-((n : ℝ) * t ^ 2) / (2 * xiS c 1)))) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => gaussMeas n {α | ε ≤ |En c n α - ∫ a, En c n a ∂(gaussMeas n)|}) atTop (𝓝 0)) := by sorry

end QPSpinParisi
