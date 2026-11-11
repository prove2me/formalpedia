-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_5_7
-- name    : QuantumXoP.Security.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:36.922752+00:00
-- url     : https://prove2.me/theorems/52b2fe8d-3dda-40e9-a4f7-217fcfef2a6b
-- title:
--   Lemma 5.7 — recursion for the Fourier coefficients of a random permutation
-- statement:
--   Let $2\le d\le N$ and let $\gamma\in\widehat F$ satisfy $|\gamma|=d$, with $\mathrm{supp}(\gamma)=\{x_1,\dots,x_d\}$ and $\gamma^{(i\leftarrow d)}$ as on p. 22. Then
--   $$\widehat\mu_P(\gamma)=-\frac{1}{N-d+1}\sum_{i=1}^{d-1}\widehat\mu_P\big(\gamma^{(i\leftarrow d)}\big).$$
--
--   It drives the proof of the maximal-magnitude bound, Lemma 5.4.
--
--   **Formalization Note** The recursion is stated for every enumeration of the support; the paper uses the lexicographically increasing one.
--
--   Differences from the source:
--   - generalization: §5 assumes n ≥ 5 throughout (p. 14) → every n : ℕ (the other hypotheses only); reason: an exact identity, stated without the standing assumption; it specializes to every n ≥ 5
--   - generalization: supp(γ) = {x_1 < ⋯ < x_d} listed in increasing order → every enumeration e : Fin d ≃ supp(γ); reason: the increasing enumeration is one of them, so the statement specializes to the source
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 22 (PDF p. 24), Lemma 5.7 and the definition of γ^{(i←d)} before it

import Mathlib
import Definitions.Def_QuantumXoP_Security_Fourier

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 5.7 (p. 22): for `2 ≤ d ≤ N` and `|γ| = d` with `supp(γ) = {x_1, …, x_d}` (any
enumeration `e`), `μ̂_P(γ) = −(1/(N − d + 1)) Σ_{i=1}^{d−1} μ̂_P(γ^{(i←d)})`. -/
theorem lemma_5_7 {n d : ℕ} (hd : 2 ≤ d) (hdN : d ≤ 2 ^ n) (γ : Fn n) (hγ : charDeg γ = d)
    (e : Fin d ≃ supp γ) :
    fourierCoeff (density (permLaw n)) γ =
      -((((2 : ℝ) ^ n - d + 1 : ℝ) : ℂ))⁻¹ *
        ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < d - 1),
          fourierCoeff (density (permLaw n))
            (shiftChar γ (e i : Qubits n) (e ⟨d - 1, by omega⟩ : Qubits n)) := by sorry

end QuantumXoP.Security
