-- Prove2me | Theorems.Thm_SpectrumLB_lemma_6_7
-- name    : SpectrumLB.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:37:23.844718+00:00
-- url     : https://prove2.me/theorems/38c60f54-3f1a-4b14-9385-11f684de6a84
-- title:
--   Lemma 6.7 — counting pairs in a conjugacy class and $|\sigma\tau|\ge\max\{2,2u-2c(\mu)\}$
-- statement:
--   Let $\mu\ne\varnothing$ be a non-trivial cycle type with support size $s=s(\mu)$, $C_\mu$ its conjugacy class in $S_n$, and $u\ge0$.
--
--   1. The number of ordered pairs $(\sigma,\tau)\in C_\mu\times C_\mu$ with $|\mathrm{supp}(\sigma)\setminus\mathrm{supp}(\tau)|=|\mathrm{supp}(\tau)\setminus\mathrm{supp}(\sigma)|=u$ is at most $C_s\,n^{s+u}$, with $C_s$ depending only on $s$.
--   2. For any such pair with $\sigma\ne\tau^{-1}$,
--   $$
--   |\sigma\tau|\ \ge\ \max\{2,\ 2u-2c(\mu)\}.
--   $$
--   3. If moreover $u=c(\mu)+1$ and $|\mu|$ is even, then $|\sigma\tau|\ge4$.
--
--   Here $|\cdot|$ is the Cayley length and $c(\mu)$ the number of non-trivial cycles. These counting and length bounds control the second moment of $\mathcal P^\circ_m$ in Lemma 6.3.
--
--   Differences from the source:
--   - encoding: C_μ for a non-trivial cycle type μ → permutations with the cycle type of a fixed π₀ ≠ 1, s(μ) = |supp π₀|; reason: same set
--   - encoding: O_s(n^{s+u}) → ∃ C depending on s only, chosen before n, u and μ; reason: meaning of the subscript s
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Lemma 6.7, Eqs. (6.44)–(6.46), pp. 28–29

import Mathlib
import Definitions.Def_SpectrumLB_cayleyLen
import Definitions.Def_SpectrumLB_ntCycles

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Lemma 6.7 (pairs in a conjugacy class).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Lemma 6.7, Eqs. (6.44)–(6.46), pp. 28–29: "For a non-trivial cycle type μ ≠ ∅ and support size
s = s(μ), the number of ordered pairs (σ, τ) ∈ C_μ × C_μ with |supp(σ) ∖ supp(τ)| = |supp(τ) ∖ supp(σ)| = u
is O_s(n^{s+u}). For any such pair, if σ ≠ τ^{−1}, then |στ| ≥ max{2, 2u − 2c(μ)}. Moreover, if
u = c(μ) + 1 and |μ| is even, then |στ| ≥ 4."

**Formalization Note.** `C_μ` is the set of permutations with the cycle type of a fixed `π₀ ≠ 1`
(`μ ≠ ∅`); `s(μ) = |supp π₀|`, `c(μ) = ntCycles`, `|μ| = cayleyLen`. In (a) the constant depends on `s`
only, before `n`, `u` and `μ`. The inequality of (b) is in `ℤ`. -/
theorem lemma_6_7 :
    (∀ s : ℕ, ∃ C : ℝ, ∀ n u : ℕ, ∀ π₀ : Equiv.Perm (Fin n), π₀ ≠ 1 → π₀.support.card = s →
      (((Finset.univ : Finset (Equiv.Perm (Fin n) × Equiv.Perm (Fin n))).filter fun p =>
          p.1.cycleType = π₀.cycleType ∧ p.2.cycleType = π₀.cycleType ∧
          (p.1.support \ p.2.support).card = u ∧ (p.2.support \ p.1.support).card = u).card : ℝ) ≤
        C * (n : ℝ) ^ (s + u)) ∧
    (∀ n u : ℕ, ∀ σ τ : Equiv.Perm (Fin n), σ ≠ 1 → σ.cycleType = τ.cycleType →
      (σ.support \ τ.support).card = u → (τ.support \ σ.support).card = u → σ ≠ τ⁻¹ →
        max 2 (2 * (u : ℤ) - 2 * ntCycles σ) ≤ (cayleyLen (σ * τ) : ℤ)) ∧
    (∀ n u : ℕ, ∀ σ τ : Equiv.Perm (Fin n), σ ≠ 1 → σ.cycleType = τ.cycleType →
      (σ.support \ τ.support).card = u → (τ.support \ σ.support).card = u →
      u = ntCycles σ + 1 → Even (cayleyLen σ) → 4 ≤ cayleyLen (σ * τ)) := by sorry

end SpectrumLB
