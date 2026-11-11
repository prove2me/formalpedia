-- Prove2me | Theorems.Thm_PelagicFF_lemma_3_2
-- name    : PelagicFF.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:54:57.129831+00:00
-- url     : https://prove2.me/theorems/c233e455-7a5d-436b-a71e-2a85097fd98f
-- title:
--   Lemma 3.2 — sampled inner-product estimator, $\mathbb E(\widehat L(v)-\langle v,W\rangle)^2\le\frac Nk\|v\|_2^2$
-- statement:
--   Let $W$ be a random variable over $\{-1,1\}^N$ and, independently of $W$, sample $I_1,\dots,I_k$ uniformly from $[N]$ with replacement. For a fixed $v\in\mathbb R^N$ let
--   $$\widehat L(v)=\frac1k\sum_{j=1}^k N\,v_{I_j}W_{I_j}.$$
--   Then
--   $$\mathbb E\big(\widehat L(v)-\langle v,W\rangle\big)^2\ \le\ \frac Nk\,\|v\|_2^2 .$$
--
--   It controls the first error term in the decomposition of Lemma 4.3.
--
--   **Formalization Note** $[N]$ is a nonempty finite type $\iota$ with $N=|\iota|$; the expectation is the finite sum against $\mathrm{law}(W)\otimes\mathrm{Unif}(\iota)^{\otimes k}$.
--
--   Differences from the source:
--   - encoding: random variables on {−1,1}^N → laws (PMF) on ι → Bool for a finite coordinate type ι with N = card ι, bit b read as sign b; reason: relabelling coordinates and values changes no instance
--   - encoding: indices sampled from [N]; k samples → a nonempty finite index type ι with N = card ι; 0 < k; reason: uniform sampling from [N] and the factor 1/k are defined only for N ≥ 1 and k ≥ 1; excludes undefined cases only
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.2, eq. (4), p.19

import Mathlib
import Definitions.Def_Cotype

open OAI.Cotype

namespace PelagicFF

/-- **Lemma 3.2.** Let `W` be a random variable over `{−1,1}^N`, sample `I₁, …, I_k` independently
and uniformly from `[N]` with replacement, independently of `W`, and for a fixed `v ∈ ℝ^N` let
`L̂(v) = (1/k) ∑_j N v_{I_j} W_{I_j}`. Then `E(L̂(v) − ⟨v, W⟩)² ≤ (N/k)‖v‖₂²`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.2, eq. (4), p.19.

**Formalization Note.** `[N]` is a nonempty finite type `ι` with `N = card ι`, and `{−1,1}^N` is
`ι → Bool`. The expectation is the finite sum against `μ ⊗ Unif(ι)^{⊗k}`. `0 < k` excludes the
undefined `1/k` at `k = 0`. -/
theorem lemma_3_2 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (μ : PMF (ι → Bool))
    (k : ℕ) (hk : 0 < k) (v : ι → ℝ) :
    ∑ w, ∑ I : Fin k → ι, (μ w).toReal * ((Fintype.card ι : ℝ) ^ k)⁻¹ *
        ((k : ℝ)⁻¹ * ∑ j, (Fintype.card ι : ℝ) * v (I j) * sign (w (I j)) -
          ∑ i, v i * sign (w i)) ^ 2 ≤
      (Fintype.card ι : ℝ) / k * ∑ i, v i ^ 2 := by sorry

end PelagicFF
