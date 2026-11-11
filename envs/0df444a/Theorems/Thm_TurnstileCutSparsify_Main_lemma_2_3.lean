-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_lemma_2_3
-- name    : TurnstileCutSparsify.Main.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:38:55.80289+00:00
-- url     : https://prove2.me/theorems/970a5a60-7faf-4855-8bcb-5762cb75353f
-- title:
--   Lemma 2.3 — projection counting: at most n^{2α} distinct projections onto λ₀-heavy edges among cuts of weight ≤ αλ₀
-- statement:
--   Let $G$ (nonnegative integer weights on $n\ge2$ vertices) be connected, let $\lambda_0>0$, and let $F^\star\subseteq E$ be a set of edges with $\lambda_e\ge\lambda_0$ for every $e\in F^\star$. For every real $\alpha\ge1$, the sets $E(S,V\setminus S)\cap F^\star$, over all $\emptyset\neq S\subsetneq V$ with $w(S,V\setminus S)\le\alpha\lambda_0$, take at most $n^{2\alpha}$ distinct values:
--   $$\#\{E(S,V\setminus S)\cap F^\star:\ \emptyset\ne S\subsetneq V,\ w(S,V\setminus S)\le\alpha\lambda_0\}\le n^{2\alpha}.$$
--   It is the union-bound count behind (22)–(23).
--
--   Differences from the source:
--   - encoding: vertices V = [n]; coordinates = the N unordered pairs; graphs G = (V, E, w) → vertices Fin n (0-based); Pair n = {(u, v) : u < v}; a graph is a weight function on Pair n (E = pairs of positive weight); reason: same graphs; the canonical pair order is not needed by the statement
--   - encoding: G connected; integer weights (standing, §2) → (supportGraph (toR w)).Connected for w : Pair n → ℕ; n^{2α} a real power; reason: same instances
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Lemma 2.3, p. 10

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph

open scoped BigOperators Classical

namespace TurnstileCutSparsify.Main

/-- **Lemma 2.3** (Projection counting; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 10).
Let `G` (nonnegative integer weights `w` on `n ≥ 2` vertices) be connected, let `lam0 > 0`, and let
`F⋆ ⊆ E` be a set of edges with `λ_e ≥ lam0` for every `e ∈ F⋆`. For every real `α ≥ 1`, the sets
`E(S, V \ S) ∩ F⋆`, over all `∅ ≠ S ⊊ V` with `w(S, V \ S) ≤ α lam0`, take at most `n^{2α}`
distinct values. -/
theorem lemma_2_3 (n : ℕ) (hn : 2 ≤ n) (w : Pair n → ℕ)
    (hconn : (supportGraph (toR w)).Connected) (lam0 : ℝ) (hlam0 : 0 < lam0) (Fs : Finset (Pair n))
    (hFs : ∀ e ∈ Fs, 0 < w e ∧ lam0 ≤ conn (toR w) e) (α : ℝ) (hα : 1 ≤ α) :
    ((((Finset.univ : Finset (Finset (Fin n))).filter fun S =>
        S.Nonempty ∧ S ≠ Finset.univ ∧ cut (toR w) S ≤ α * lam0).image
          fun S => cutEdges (toR w) S ∩ Fs).card : ℝ) ≤ (n : ℝ) ^ (2 * α) := by sorry

end TurnstileCutSparsify.Main
