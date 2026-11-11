-- Prove2me | Theorems.Thm_RandModSubsetSum_lemma_4_2
-- name    : RandModSubsetSum.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:34.058227+00:00
-- url     : https://prove2.me/theorems/378b2bd7-9580-43e7-afd1-4dc9831642f7
-- title:
--   Lemma 4.2 — $\mathrm{Var}(Z)/\mathbb E(Z)^2\le\sum_{W\subsetneq H}\mu_W\prod_ip_i^{s_i(W)}$
-- statement:
--   Let $\mathcal D$ be a finite nonempty family of representations of the root $x$, let $Z$ count its members matching all residue labels in the auxiliary residue model, and let $p_1,\dots,p_7$ be distinct primes with $p_i>127!\,6^{127}$ (7). Then
--
--   $$\frac{\mathrm{Var}(Z)}{\mathbb E(Z)^2}\le\sum_{W\in\mathcal W,\ W\subsetneq H}\mu_W\prod_{i=1}^7p_i^{s_i(W)},$$
--
--   where $\mathcal W$ is the family of difference spans of $\mathcal D$, $s_i(W)=2^i-1-\dim\pi_iW$, and $\mu_W$ is the largest relative size of a $W$-coset. With $\log_2p_i=(K_i-K_{i+1})n+O(1)$ the product is $2^{n\sum_i\chi_iK_i+O(1)}$, which is the printed form.
--
--   By Chebyshev, the right-hand side bounds $\Pr(Z=0)$ (8); the residue factor depends only on the difference ranks, and the exact types enter only through $\mu_W$.
--
--   Differences from the source:
--   - generalization: 𝒟 the exact-type family of x → any finite nonempty family of representations of x; reason: the proof uses only that the members are representations of x; the source's family is a special case
--   - generalization: μ_W 2^{n Σ_i χ_i K_i + O(1)} → μ_W Π_i p_i^{s_i(W)}; reason: the exact bound of the proof (p. 21); it implies the printed one when log₂ p_i = (K_i − K_{i+1})n + O(1)
--   - encoding: W ⊊ H → W ≠ H; reason: every difference span lies in H
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Lemma 4.2, p. 20; (7), p. 20; proof, p. 21

import Mathlib
import Definitions.Def_RandModSubsetSum_Template

open scoped BigOperators

namespace RandModSubsetSum

open Classical in
/-- **Lemma 4.2** (normalized variance through difference spans). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Lemma 4.2, p. 20, with (7),
p. 20, and the exact bound of its proof, p. 21.

Let `𝒟` be a finite nonempty family of representations of the root `x`, let `Z` count its members
matching all residue labels in the auxiliary residue model, and let the moduli `p_1, …, p_7` be
distinct primes with `p_i > 127! · 6^{127}` (7). Then
`Var(Z)/E(Z)² ≤ Σ_{W ∈ 𝒲, W ⊊ H} μ_W Π_{i=1}^7 p_i^{s_i(W)}`.

Since `log₂ p_i = (K_i − K_{i+1}) n + O(1)` gives `Π_i p_i^{s_i} = 2^{n Σ_i χ_i K_i + O(1)}`, this is
the printed bound `Σ_{W ⊊ H} μ_W 2^{n Σ_i χ_i K_i + O(1)}`.

**Formalization Note.** Every `W ∈ 𝒲` lies in `H`, so `W ⊊ H` is `W ≠ H`. Index `i : Fin 7` stands
for depth `i + 1`. `s_i` is an integer exponent (`zpow`). -/
theorem lemma_4_2 {n : ℕ} (p : Fin 7 → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (h7 : ∀ i, Nat.factorial 127 * 6 ^ 127 < p i) (x : Fin n → Fin 2) (𝒟 : Finset (Rep n))
    (hne : 𝒟.Nonempty) (hrep : ∀ D ∈ 𝒟, IsRepOf x D) :
    varRatio p x 𝒟 ≤
      ∑ W ∈ (spans 𝒟).filter (fun W => W ≠ sumZero),
        muW 𝒟 W * ∏ i : Fin 7, (p i : ℝ) ^ (sDef W (i.val + 1)) := by sorry

end RandModSubsetSum
