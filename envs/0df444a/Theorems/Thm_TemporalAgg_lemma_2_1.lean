-- Prove2me | Theorems.Thm_TemporalAgg_lemma_2_1
-- name    : TemporalAgg.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:47.143203+00:00
-- url     : https://prove2.me/theorems/78512e0d-2e72-474c-b24a-e65c913f4707
-- title:
--   Lemma 2.1 — splicing k inputs costs at most k·L
-- statement:
--   Let $f$ be a load function on $\mathcal U^n$, let $k\ge1$, and let $x^1,\dots,x^k\in\mathcal U^n$ satisfy $f(x^j)\le L$ for every $j$. Then every $z\in\mathcal U^n$ such that for every coordinate $i$ there is some $j$ with $z_i=x^j_i$ satisfies
--
--   $$
--   f(z_1,\dots,z_n)\le k\cdot L .
--   $$
--
--   This is the splicing lemma: a vector assembled coordinatewise from $k$ low-load vectors has load at most $k$ times as large. It turns "few groups" (Lemma 3.1) into a load bound (Lemma 3.2).
--
--   **Formalization Note** The vectors are indexed by $\mathrm{Fin}\,k$; $L$ is any real number.
--
--   Differences from the source:
--   - reading: k input vectors {(x^j_1, …, x^j_n)}_{j∈[k]} → 0 < k; reason: k input vectors means k ≥ 1; at k = n = 0 the conclusion f(z) ≤ 0 is false for f ≡ 1
--   - encoding: f : 𝒰ⁿ → ℝ≥0 (Definition 1.1) → f : (Fin n → U) → ℝ satisfying the splice inequality; reason: the splice inequality with x = y = z gives f ≥ 0, so the instances are the same
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), Lemma 2.1, p.15

import Mathlib
import Definitions.Def_TemporalAgg_IsLoadFunction

namespace TemporalAgg

/-- **Lemma 2.1** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against Adaptive
Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, p.15).

Let `f` be a load function and `x¹, …, xᵏ ∈ 𝒰ⁿ` with `f(xʲ) ≤ L` for every `j`. Then every
`z ∈ 𝒰ⁿ` with `zᵢ = xʲᵢ` for some `j` (for every `i`) satisfies `f z ≤ k · L`.

**Formalization Note** The `k` vectors are indexed by `Fin k`, with `0 < k` ("k input
vectors … j ∈ [k]"); at `k = 0`, `n = 0` the bound `f z ≤ 0` would fail for `f ≡ 1`. -/
theorem lemma_2_1 {U : Type*} {n k : ℕ} (f : (Fin n → U) → ℝ) (hf : IsLoadFunction f)
    (hk : 0 < k) (x : Fin k → Fin n → U) (L : ℝ) (hx : ∀ j, f (x j) ≤ L)
    (z : Fin n → U) (hz : ∀ i, ∃ j, z i = x j i) :
    f z ≤ (k : ℝ) * L := by sorry

end TemporalAgg
