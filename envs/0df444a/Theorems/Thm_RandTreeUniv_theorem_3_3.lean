-- Prove2me | Theorems.Thm_RandTreeUniv_theorem_3_3
-- name    : RandTreeUniv.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:11:31.571098+00:00
-- url     : https://prove2.me/theorems/52546a9e-ae8d-4eea-86eb-4f20e778b144
-- title:
--   Theorem 3.3 — optimal-depth spanning path systems in $G(n,C_0(\ln n)^\psi/n)$
-- statement:
--   Let $C_0=10^5$ and $C^*=2(1+10^{-100})$ (display (3)). Let $\psi=\psi(n)\in[1,\ln n/(4\ln\ln n)]$, $k^*=\lceil C^*\ln n/(\psi\ln\ln n)\rceil$, let $k\ge k^*$ be an integer with $k+1\mid n$, and $m=n/(k+1)$. Let $p=C_0(\ln n)^\psi/n$ and let $\mathbf a,\mathbf c$ be disjoint $m$-tuples of distinct vertices of $[n]$. Then
--
--   $$
--   \mathbb P\big(G(n,p)\text{ contains an }(\mathbf a,\mathbf c;k)\text{-path system}\big)=1-o\big(1/(\ln\ln n)^2\big).
--   $$
--
--   The path system is spanning, since $m(k+1)=n$. Combined with Lemma 3.2 this gives linking systems of depth $\Theta(\ln n/(\psi\ln\ln n))$, optimal up to the constant.
--
--   Differences from the source:
--   - reading: whp / o(·) for fixed functions ψ(n), k(n) and fixed tuples → uniform over all admissible ψ, k and tuples at each n (for every ε > 0 there is N such that …); reason: equivalent: a non-uniform failure yields a choice of functions and tuples along which the paper's statement fails
--   - encoding: vertex set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabelling; same graphs up to isomorphism
--   - encoding: G(n,p) with p = p(n) a probability → published erProb n p, which clamps p to [0,1]; reason: the clamp is the identity on [0,1], and the edge probabilities used lie in [0,1] for all large n
--   - encoding: disjoint vertex m-tuples (tuples of distinct vertices, §1.3) → injective maps Fin (n/(k+1)) → Fin n with disjoint ranges; reason: same tuples
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), display (3), §3.1 and Theorem 3.3, p.14 (PDF 15)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_RandTreeUniv_IsPathSystemIn
import Definitions.Def_RandTreeUniv_kStar

set_option autoImplicit false

open scoped Classical
open LPCommunity.SBMRecovery

namespace RandTreeUniv

/-- **Theorem 3.3** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.14 (PDF 15)), with the constants of display (3) and the set-up of
§3.1: fix a function `ψ = ψ(n) ∈ [1, ln n/(4 ln ln n)]`, set `k∗ = ⌈C∗ ln n/(ψ ln ln n)⌉`, fix an
integer `k ≥ k∗` with `k + 1 ∣ n` and `m := n/(k + 1)`. Consider `p = C₀ (ln n)^ψ/n` and disjoint
vertex `m`-tuples `a, c ⊆ [n]`. Then
`P(G(n, p) contains an (a, c; k)-path system) = 1 − o(1/(ln ln n)²)`.

**Formalization Note** The `o(·)` is stated uniformly: for every `ε > 0` there is `N` such that for
all `n ≥ N`, all `ψ ∈ [1, ln n/(4 ln ln n)]`, all integers `k ≥ k∗(n, ψ)` with `k + 1 ∣ n` and all
admissible tuples, `(1 − P)·(ln ln n)² ≤ ε`; this is equivalent to the paper's statement for
arbitrary choices of `ψ(n)`, `k(n)`, `a`, `c`. Tuples are injective maps
`Fin (n/(k+1)) → Fin n` with disjoint ranges (tuples of distinct vertices, §1.3). `C₀ = 10⁵`,
`C∗ = 2(1 + 10⁻¹⁰⁰)`. `(ln n)^ψ` is the real power. `G(n, p)` is the published `erProb`. -/
theorem theorem_3_3 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ ψ : ℝ, 1 ≤ ψ → ψ ≤ Real.log n / (4 * Real.log (Real.log n)) →
      ∀ k : ℕ, kStar n ψ ≤ k → (k + 1) ∣ n →
      ∀ a c : Fin (n / (k + 1)) → Fin n, Function.Injective a → Function.Injective c →
        (∀ i j, a i ≠ c j) →
        (1 - erProb n (C0 * Real.log n ^ ψ / n) (fun G => IsPathSystemIn G Set.univ a c k)) *
          Real.log (Real.log n) ^ 2 ≤ ε := by sorry

end RandTreeUniv
