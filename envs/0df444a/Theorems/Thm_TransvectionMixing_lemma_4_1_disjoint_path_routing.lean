-- Prove2me | Theorems.Thm_TransvectionMixing_lemma_4_1_disjoint_path_routing
-- name    : TransvectionMixing.lemma_4_1_disjoint_path_routing
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:01.017565+00:00
-- url     : https://prove2.me/theorems/9db9aa4f-fc68-4805-8343-88ae4753ceba
-- title:
--   Lemma 4.1 — disjoint-path routing in the time-expanded graph
-- statement:
--   Let $1\le k<n$ and $\mathcal B,\mathcal T\subseteq[n]$ with $|\mathcal B|=|\mathcal T|=k$.
--
--   1. For every $\zeta\in(0,1/4]$ and every integer
--   $$
--   T\ \ge\ 8\,\frac{n^2}{n-k}\log\frac n\zeta ,
--   $$
--   the time-expanded graph of a uniformly random skeleton of length $T$ contains, with probability at least $1-\zeta$, $k$ vertex-disjoint directed paths from $\{(b,0):b\in\mathcal B\}$ to $\mathcal T\times\{T\}$.
--   2. If $\zeta\le(16n)^{-1}$, the same holds for every integer $T\ge\frac92\,\frac{n^2}{n-k}\log\frac n\zeta$.
--
--   Routing basis rows to target rows is what makes the source minors of the section constructions nonsingular (burn-in).
--
--   **Formalization Note** The target set $\mathcal T$ is `Tg` in Lean (the paper also writes $T$ for the length).
--
--   Differences from the source:
--   - encoding: k vertex-disjoint directed paths in the time-expanded graph → a family indexed by ℬ of row sequences p(0..T) obeying the edge rule, starting at b, ending in 𝒯, injective in every layer; reason: paths through a layered graph meet each layer once, so vertex-disjointness is layerwise injectivity
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Lemma 4.1, eq. (15), p.13

import Mathlib
import Definitions.Def_TransvectionMixing_walkMat
import Definitions.Def_TransvectionMixing_HasDisjointPaths

namespace TransvectionMixing

/-- **Lemma 4.1** (disjoint-path routing) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §4, p.13). Let `1 ≤ k < n` and `ℬ, 𝒯 ⊆ [n]`
satisfy `|ℬ| = |𝒯| = k`. For every `ζ ∈ (0, 1/4]` and every integer
`T ≥ 8 (n²/(n − k)) log(n/ζ)`, the time-expanded graph of a uniform random skeleton of length
`T` contains, with probability at least `1 − ζ`, `k` vertex-disjoint directed paths from
`{(b, 0) : b ∈ ℬ}` to `𝒯 × {T}`. Moreover, if `ζ ≤ (16n)⁻¹`, one may take
`T ≥ (9/2)(n²/(n − k)) log(n/ζ)` (eq. (15)).

**Formalization Note** The target set `𝒯` is `Tg` (the paper overloads `T`). -/
theorem lemma_4_1_disjoint_path_routing (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n)
    (B Tg : Finset (Fin n)) (hB : B.card = k) (hTg : Tg.card = k) :
    (∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 / 4 → ∀ T : ℕ,
        8 * ((n : ℝ) ^ 2 / ((n : ℝ) - k)) * Real.log (n / ζ) ≤ T →
        1 - ζ ≤ prob (fun σ : Skel n T => HasDisjointPaths σ B Tg)) ∧
      (∀ ζ : ℝ, 0 < ζ → ζ ≤ (16 * (n : ℝ))⁻¹ → ∀ T : ℕ,
        9 / 2 * ((n : ℝ) ^ 2 / ((n : ℝ) - k)) * Real.log (n / ζ) ≤ T →
        1 - ζ ≤ prob (fun σ : Skel n T => HasDisjointPaths σ B Tg)) := by sorry

end TransvectionMixing
