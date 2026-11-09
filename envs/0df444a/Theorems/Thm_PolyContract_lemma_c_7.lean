-- Prove2me | Theorems.Thm_PolyContract_lemma_c_7
-- name    : PolyContract.lemma_c_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:54:44.97922+00:00
-- url     : https://prove2.me/theorems/049b9e7d-589c-4ecb-bc9b-26e16aa19bfd
-- title:
--   Lemma C.7 — common contacts are the subset sums
-- statement:
--   Let $(a,T)$ be a Subset Sum instance with $k\ge1$ and $a\in\mathbb Z^k_{>0}$, with $0\le T\le\sum_ia_i$; let $N_0\in\mathbb Z$, $\delta_1>0$ and $H:=10\sum_ia_i+1$. Define $\mu,\mu'\in\mathbb Z^k_{>0}$ by $\mu_i:=H8^{i-1}+a_i$, $\mu'_i:=H8^{i-1}$, and
--   $$\Gamma_1:=\{\delta_1(N_0+\mu^\top\chi):\chi\in\{0,1\}^k\},\qquad \Gamma_2:=\{\delta_1(N_0+T+\mu'^\top\chi'):\chi'\in\{0,1\}^k\}.$$
--   Then the common points of $\Gamma_1$ and $\Gamma_2$ are the points $\delta_1(N_0+\mu^\top\chi)$ with $a^\top\chi=T$. In particular, $\Gamma_1$ and $\Gamma_2$ meet if and only if $(a,T)$ is a yes-instance. Moreover, $\mu$ and $\mu'$ are perturbed powers of 8.
--
--   This is the arithmetic core of the reduction: two combs whose contacts are $\Gamma_1$ and $\Gamma_2$ touch their lines simultaneously exactly at solutions.
--
--   Differences from the source:
--   - generalization: the lemma's conclusion (common points; meet iff yes-instance) → the same conclusion plus µ, µ′ ∈ F; reason: µ, µ′ ∈ F is the last line of the lemma's proof on p.52 and is used by Proposition C.9; the statement implies the source's
--   - encoding: µ, a ∈ Z^k indexed from 1; χ ∈ {0,1}^k → lists of naturals indexed from 0; χ a list of booleans of length k; reason: Lean convention; same instances
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Lemma C.7, p.52 (PDF p.53), with the last line of its proof

import Mathlib
import Definitions.Def_PolyContract_IsComb

set_option autoImplicit false

namespace PolyContract

/-- **Lemma C.7** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, p.52), for a Subset Sum instance `(a, T)` with `k ≥ 1` and `a ∈ ℤ^k_{>0}`: let
`0 ≤ T ≤ Σ_i a_i`, `N₀ ∈ ℤ`, `δ₁ > 0`, `H := 10 Σ_i a_i + 1`, `µ_i := H 8^{i−1} + a_i`,
`µ′_i := H 8^{i−1}`, `Γ₁ := {δ₁(N₀ + µ⊤χ) : χ ∈ {0, 1}^k}` and
`Γ₂ := {δ₁(N₀ + T + µ′⊤χ′) : χ′ ∈ {0, 1}^k}`. Then the common points of `Γ₁` and `Γ₂` are the
points `δ₁(N₀ + µ⊤χ)` with `a⊤χ = T`; in particular `Γ₁` and `Γ₂` meet iff `(a, T)` is a
yes-instance. Moreover `µ, µ′ ∈ F` (the last line of the proof, p.52).

**Formalization Note** `a` is a nonempty list of positive naturals; `χ` is a list of booleans of
length `k`; indices start at `0`, so `µ_i = H 8^i + a_i`. -/
theorem lemma_c_7 (a : List ℕ) (ha : a ≠ []) (hpos : ∀ x ∈ a, 0 < x) (T : ℤ) (hT0 : 0 ≤ T)
    (hT : T ≤ (a.sum : ℤ)) (N₀ : ℤ) (δ₁ : ℝ) (hδ : 0 < δ₁) :
    (∀ γ : ℝ, γ ∈ contacts δ₁ N₀ (itemWeights a) ∩ contacts δ₁ (N₀ + T) (baseWeights a) ↔
      ∃ χ : List Bool, χ.length = a.length ∧
        γ = δ₁ * ((N₀ : ℝ) + (selSum (itemWeights a) χ : ℝ)) ∧ (selSum a χ : ℤ) = T) ∧
    ((contacts δ₁ N₀ (itemWeights a) ∩ contacts δ₁ (N₀ + T) (baseWeights a)).Nonempty ↔
      IsYesInstance a T) ∧
    PerturbedPow8 (itemWeights a) ∧ PerturbedPow8 (baseWeights a) := by sorry

end PolyContract
