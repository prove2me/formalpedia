-- Prove2me | Theorems.Thm_SaglamGV_prob_subset_ker
-- name    : SaglamGV.prob_subset_ker
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:49:17.62059+00:00
-- url     : https://prove2.me/theorems/b47e2de4-2224-4669-9bf6-5b003725bfce
-- title:
--   $\Pr[S\subseteq\ker M]=2^{-m(\ell-1)}=(\tau/V)^{\ell-1}$ for an $\ell$-element circuit
-- statement:
--   Let $M$ be uniform on $\mathbb F_2^{m\times n}$ and let $S\subseteq B_d$ be a circuit with $\ell$ elements. Then, with $\tau=V2^{-m}$,
--
--   $$
--   \Pr[S\subseteq\ker M]=2^{-m(\ell-1)}=\Big(\frac\tau V\Big)^{\ell-1}.
--   $$
--
--   The span of $S$ has dimension $\ell-1$, and a uniform matrix kills a fixed $k$-dimensional subspace with probability $2^{-mk}$.
--
--   Differences from the source:
--   - generalization: the integer m chosen in §2 with (1 − ζ)R/2 ≤ τ < (1 − ζ)R, inside the regime of §2 → every m ∈ ℕ and every n, d; reason: the identity holds for every m; it specializes to the chosen one
--   - encoding: Pr over M uniform on 𝔽₂^{m×n} → probM: the fraction of the 2^{mn} matrices; reason: uniform probability on a finite set; same values
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §2, p.2 (display Pr[S ⊆ ker M] = 2^{−m(ℓ−1)} = (τ/V)^{ℓ−1})

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Params
import Definitions.Def_SaglamGV_Circuit

namespace SaglamGV

open Matrix

/-- The kernel probability of a circuit (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §2, p.2: "Since the span of an ℓ-element circuit has
dimension ℓ − 1, Pr[S ⊆ ker M] = 2^{−m(ℓ−1)} = (τ/V)^{ℓ−1}").

For $M$ uniform on $𝔽_2^{m×n}$ and every $ℓ$-element circuit $S ⊆ B_d$,
$\Pr[S ⊆ \ker M] = 2^{−m(ℓ−1)} = (τ/V)^{ℓ−1}$ with $τ = V 2^{−m}$.

**Formalization Note** Stated for every $m$ (not only the $m$ chosen in §2); $S ⊆ \ker M$ is
$Mx = 0$ for all $x ∈ S$. -/
theorem prob_subset_ker (n d m ℓ : ℕ) (S : Finset (Fin n → ZMod 2)) (hS : S ∈ circuits n d ℓ) :
    probM (fun M : Matrix (Fin m) (Fin n) (ZMod 2) => ∀ x ∈ S, M *ᵥ x = 0) =
        ((2 : ℝ) ^ (m * (ℓ - 1)))⁻¹ ∧
      ((2 : ℝ) ^ (m * (ℓ - 1)))⁻¹ = (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) := by sorry

end SaglamGV
