-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_5_3
-- name    : QuantumXoP.Security.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:27.400922+00:00
-- url     : https://prove2.me/theorems/e506e558-3be2-4fb0-908e-8d6c50a73de4
-- title:
--   Lemma 5.3 — the Fourier coefficient of a random permutation as an average over distinct tuples
-- statement:
--   Let $\gamma\in\widehat F$ have $|\gamma|=d$ and $\mathrm{supp}(\gamma)=\{x_1,\dots,x_d\}$. Then
--   $$\widehat\mu_P(\gamma)=\mathbb E_{(z_1,\dots,z_d)\leftarrow(\{0,1\}^n)^{(*d)}}\Big[\prod_{i=1}^d\chi_{\gamma(x_i)}(z_i)\Big],$$
--   the expectation over pairwise distinct $z_1,\dots,z_d$.
--
--   All bounds on $\widehat\mu_P$ in §5 start from this formula.
--
--   **Formalization Note** The labelling of the support is an arbitrary bijection $[d]\to\mathrm{supp}(\gamma)$, as in the statement; the expectation is the average over injections $[d]\to\{0,1\}^n$.
--
--   Differences from the source:
--   - generalization: §5 assumes n ≥ 5 throughout (p. 14) → every n : ℕ (the other hypotheses only); reason: an exact identity, stated without the standing assumption; it specializes to every n ≥ 5
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 15 (PDF p. 17), Lemma 5.3

import Mathlib
import Definitions.Def_QuantumXoP_Security_Fourier

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 5.3 (p. 15): for `|γ| = d` and any enumeration `supp(γ) = {x_1, …, x_d}`,
`μ̂_P(γ) = E_{(z_1,…,z_d) ← ({0,1}^n)^{(∗d)}}[∏_i χ_{γ(x_i)}(z_i)]` (sampling without replacement). -/
theorem lemma_5_3 {n d : ℕ} (γ : Fn n) (hγ : charDeg γ = d) (e : Fin d ≃ supp γ) :
    fourierCoeff (density (permLaw n)) γ =
      ((Fintype.card (Fin d ↪ Qubits n) : ℂ))⁻¹ *
        ∑ z : Fin d ↪ Qubits n, ∏ i : Fin d, chiStr (γ (e i : Qubits n)) (z i) := by sorry

end QuantumXoP.Security
