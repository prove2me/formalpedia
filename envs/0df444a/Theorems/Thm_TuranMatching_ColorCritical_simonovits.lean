-- Prove2me | Theorems.Thm_TuranMatching_ColorCritical_simonovits
-- name    : TuranMatching.ColorCritical.simonovits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:49.684974+00:00
-- url     : https://prove2.me/theorems/c4290116-d8ee-4b95-8d0c-67b428720f40
-- title:
--   Simonovits (1968), cited p. 5 — for color-critical H with χ(H)=k+1, an H-free graph on N ≥ N₀(H) vertices has at most t(N,k) edges
-- statement:
--   Let $k\ge 2$ and let $H$ be a finite color-critical graph of chromatic number $k+1$. Then there is $N_0=N_0(H)$ such that for every $N\ge N_0$, every $H$-free graph $G$ on $N$ vertices satisfies
--   $$|E(G)|\le t(N,k),$$
--   where $t(N,k)$ is the number of edges of the Turán graph $T(N,k)$.
--
--   This is the theorem of M. Simonovits [3] (*A method for solving extremal problems in graph theory, stability problems*, Theory of Graphs, Tihany 1966, Academic Press 1968) that the proof of Proposition 3.1 cites, in the form used there: it is applied to the subgraph induced on $X\cup Z$, which has $s+\lfloor s/(k-1)\rfloor\ge s>s_0(H)$ vertices. It is a cited classical theorem, not a result of the paper.
--
--   **Formalization Note** "$H$-free" means no (not necessarily induced) subgraph copy of $H$. Chromatic numbers are in $\mathbb N\cup\{\infty\}$, and the hypothesis fixes $\chi(H)=k+1$ as a finite value. Since $T(N,k)$ is $k$-colorable and hence $H$-free, the bound is Simonovits' equality $\mathrm{ex}(N,H)=t(N,k)$; only the upper bound is stated, which is what the proof uses.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 5, proof of Proposition 3.1, fifth paragraph, second sentence, citing [3] M. Simonovits, Theory of Graphs (Proc. Colloq., Tihany, 1966), Academic Press, 1968, pp. 279–319

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

open Finset SimpleGraph

namespace TuranMatching.ColorCritical

theorem simonovits (W : Type) [Fintype W] (H : SimpleGraph W) (k : ℕ) (hk : 2 ≤ k)
    (hH : IsColorCritical H) (hχ : H.chromaticNumber = ((k + 1 : ℕ) : ℕ∞)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (G : SimpleGraph (Fin N)) [DecidableRel G.Adj], H.Free G →
      #G.edgeFinset ≤ TuranMatching.Clique.turanNum N k := by sorry

end TuranMatching.ColorCritical
