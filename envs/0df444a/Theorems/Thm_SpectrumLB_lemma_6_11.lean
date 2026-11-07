-- Prove2me | Theorems.Thm_SpectrumLB_lemma_6_11
-- name    : SpectrumLB.lemma_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:01.603573+00:00
-- url     : https://prove2.me/theorems/838a8149-466c-4cf9-bb21-931248297d10
-- title:
--   Lemma 6.11 — $\mathrm{Tr}(\pi\,\overline\rho^{(n)}_e)\le(C_0/d)^{|\pi|}$
-- statement:
--   Let $e=(e_1,\dots,e_K)$ be positive integers. There is a constant $C_0>0$, depending only on $e$, such that for every $d\ge1$ divisible by each $e_i$, every $n$ and every permutation $\pi\in S_n$,
--
--   $$
--   \mathrm{Tr}\big(\pi\,\overline\rho^{(n)}_e\big)\ \le\ \Big(\frac{C_0}{d}\Big)^{|\pi|},
--   $$
--
--   where $\overline\rho^{(n)}_e$ is the average $n$-copy state of the tilted product-of-projections ensemble (Definition 5.4) and $|\pi|$ the Cayley length. Overlaps of the average state with permutations decay geometrically in the Cayley length; this controls every term of the Jucys–Murphy expansions in Lemmas 6.3 and 6.4.
--
--   Differences from the source:
--   - generalization: e ∈ {a, b} (Proposition 5.2's sequences), C₀ depending only on k → every positive sequence e, C₀ depending only on e; reason: the proof uses only ν_e (C₀ = max ν_e^{−1}, paper.md R5); the paper's a, b are instances
--   - encoding: d a multiple of each e_i (Definition 3.4) → 0 < d and e_i ∣ d for all i; reason: Definition 3.4's standing hypothesis, made explicit
--   - encoding: Tr(π ρ̄) compared with a real number → real part of the trace; reason: the trace is real (paper.md R8)
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Lemma 6.11, Eq. (6.60), p. 31

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_permOp
import Definitions.Def_SpectrumLB_avgState
import Definitions.Def_SpectrumLB_cayleyLen

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Lemma 6.11 (permutation overlaps of the average state).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Lemma 6.11, Eq. (6.60), p. 31: "For e ∈ {a, b}, and any permutation π ∈ S_n,
Tr(π ρ̄_e^{(n)}) ≤ (C_0/d)^{|π|}, for some C_0 > 0 that depends only on k."

**Formalization Note.** Stated for every sequence `e` of positive integers (reading R5; the proof uses only
`ν_e`), with `C₀` chosen before `d, n, π`; `d ≥ 1` and `e_i ∣ d` (Definition 3.4). The trace is real (reading
R8) and its real part is taken. -/
theorem lemma_6_11 {K : ℕ} (e : Fin K → ℕ) (he : ∀ i, 0 < e i) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ d n : ℕ, 0 < d → (∀ i, e i ∣ d) → ∀ π : Equiv.Perm (Fin n),
      (OptimalSpectrum.Entangled.permOp (ι := Fin d) π * avgState d n e).trace.re ≤ (C₀ / d) ^ cayleyLen π := by sorry

end SpectrumLB
