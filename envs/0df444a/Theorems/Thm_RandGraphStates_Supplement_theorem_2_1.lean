-- Prove2me | Theorems.Thm_RandGraphStates_Supplement_theorem_2_1
-- name    : RandGraphStates.Supplement.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:21:25.539873+00:00
-- url     : https://prove2.me/theorems/1eafedff-b6cc-46d4-bd94-350b566ea496
-- title:
--   Theorem 2.1, p.4 — every graph on $n$ vertices has $\delta_{\mathrm{LC}}(G)\le 0.3413n+o(n)$
-- statement:
--   Let $\delta_{\mathrm{LC}}(G)$ be the minimum degree up to local complementation of a graph $G$. Then for every graph $G$ on $n$ vertices,
--   $$
--   \delta_{\mathrm{LC}}(G)\le 0.3413\,n+o(n),
--   $$
--   where the $o(n)$ term depends only on $n$, not on $G$: for every $\varepsilon>0$ there is $N$ such that every graph $G$ on $n\ge N$ vertices satisfies $\delta_{\mathrm{LC}}(G)\le(0.3413+\varepsilon)n$.
--
--   This improves the earlier bound $\delta_{\mathrm{LC}}(G)\le\frac38 n+o(n)$; equivalently, every $n$-qubit graph state has distance at most $0.3413n+o(n)$.
--
--   **Formalization Note** A graph on $n$ vertices is a simple graph on $\{0,\dots,n-1\}$; $0.3413$ is the exact rational $3413/10000$.
--
--   Differences from the source:
--   - encoding: δLC(G) ≤ 0.3413n + o(n) for any graph G on n vertices → ∀ ε > 0 ∃ N ∀ n ≥ N ∀ G on n vertices, δLC(G) ≤ (0.3413 + ε)n; reason: the o(n) term is a function of n alone, which is this unfolding
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Theorem 2.1, p.4; proof via Theorem 3.4, pp.10–11

import Mathlib
import Definitions.Def_RandGraphStates_alphaLC
import Definitions.Def_RandGraphStates_Supplement_deltaLC

set_option autoImplicit false

namespace RandGraphStates.Supplement

/-- **Theorem 2.1.** For any graph `G` on `n` vertices, we have `δLC(G) ≤ 0.3413n + o(n)`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript
(November 2026), Theorem 2.1, p.4.

**Formalization Note.** The `o(n)` is uniform over all graphs on `n` vertices (the theorem is
about the worst graph of each order), and is unfolded: for every `ε > 0` there is `N` such that
every graph on `n ≥ N` vertices has `δLC(G) ≤ (0.3413 + ε)n`. A graph on `n` vertices is a
`SimpleGraph (Fin n)`. `0.3413` is the exact rational `3413/10000`. -/
theorem theorem_2_1 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : SimpleGraph (Fin n),
      (deltaLC G : ℝ) ≤ (3413 / 10000 + ε) * n := by sorry

end RandGraphStates.Supplement
