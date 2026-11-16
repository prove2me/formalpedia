-- Prove2me | Theorems.Thm_SteinerNav_Supplement_theorem_6
-- name    : SteinerNav.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:14:36.061572+00:00
-- url     : https://prove2.me/theorems/8f88941e-7196-4784-b1cd-ad4f87ba081e
-- title:
--   Theorem 6 — a search budget of $k=\lceil\log_\alpha(2\Delta\max\{1,(C_\alpha+1)/\zeta\})\rceil$ moves gives a $(C_\alpha+\zeta)$-approximate nearest neighbor with $\le k+1$ scans
-- statement:
--   Let $G=(P\cup R,E)$ be a Steiner $\alpha$-navigable graph ($\alpha>1$) on a set $P$ of $n\ge2$ input points of $\mathbb R^d$, with Steiner points $R$ and no Steiner-to-Steiner edges. Let $\Delta$ be the aspect ratio of $P$, $C_\alpha=\frac{\alpha+1}{\alpha-1}$, $\zeta>0$, and
--   $$k=\Big\lceil\log_\alpha\Big(2\Delta\max\Big\{1,\frac{C_\alpha+1}{\zeta}\Big\}\Big)\Big\rceil .$$
--   Let $q\in\mathbb R^d$ be any query. Start at any input point $x_0$ and perform strict greedy descent toward $q$, stopping at a local minimum or after $k$ moves, at a vertex $x_j$ ($j\le k$), with ties broken arbitrarily. Let the candidates be any set of input points containing every input point visited by the walk and, if $x_j$ is a Steiner point, every out-neighbor of $x_j$. Then every candidate $y$ closest to $q$ satisfies
--   $$\|y-q\|\le (C_\alpha+\zeta)\,\|p-q\|\qquad\text{for every }p\in P,$$
--   that is, $y$ is a $(C_\alpha+\zeta)$-approximate nearest neighbor of $q$ in $P$, and the search uses at most $k+1$ adjacency-list scans (one per move, plus at most one to recognize an early local minimum or to scan a Steiner vertex at the cutoff).
--
--   Unlike the termination guarantee of Lemma 6.5, this bounds the work: the number of moves depends only on $\alpha$, $\Delta$ and $\zeta$, while reaching an exact greedy local minimum can take linearly many moves.
--
--   **Formalization Note** The walk, candidate sets, scan count and budget are those of `SteinerNav.Supplement.BudgetedWalk`. The guarantee holds for every walk (every tie resolution), both stopping reasons and every closest candidate. When $q\in P$ the bound forces $y=q$.
--
--   Differences from the source:
--   - generalization: "returning the closest input point evaluated" → the bound for every finite set of input points containing the visited input points and, when the final vertex is Steiner, its out-neighbors, and every closest element of it; reason: whatever the procedure evaluates (in particular the out-neighbors scanned at an early Steiner local minimum or at the cutoff) is such a set, so the statement specializes to the source's procedure.
--   - encoding: n input points → 2 ≤ |P|; reason: the paper's standing assumption (§3), under which the aspect ratio Δ is defined.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee62135a42ef49d815773f6af7f50ba344b9460d6007d849529b707b183), Theorem 6, p.24 (PDF p.24); proof pp.24–25; C_α §6.3, p.22

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_aspectRatio
import Definitions.Def_SteinerNav_GreedyRun
import Definitions.Def_SteinerNav_Supplement_BudgetedWalk

namespace SteinerNav.Supplement

/-- Theorem 6 (bounded search budget): let `G = (P ∪ R, E)` be Steiner `α`-navigable (`α > 1`) with no
Steiner-to-Steiner edges, `ζ > 0`, `k = ⌈log_α(2Δ max{1, (C_α + 1)/ζ})⌉` with `C_α = (α+1)/(α−1)` and
`Δ` the aspect ratio of `P`. For every query `q`, every strict greedy descent toward `q` that starts at
an input point and stops at a local minimum or after `k` moves, every candidate set of input points
containing the visited input points and, if the last vertex is Steiner, its out-neighbors, and every
candidate `y` closest to `q`: `‖y − q‖ ≤ (C_α + ζ)‖p − q‖` for all `p ∈ P`, and at most `k + 1`
adjacency-list scans are used (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 6, p.24; proof pp.24–25).

**Formalization Note** All tie resolutions are covered. `2 ≤ |P|` is the paper's standing assumption,
under which `Δ` is the true aspect ratio. -/
theorem theorem_6 {d : ℕ} (α : ℝ) (hα : 1 < α) (P R : Finset (Pt d)) (E : Finset (Pt d × Pt d))
    (hn : 2 ≤ P.card) (hG : IsSteinerNavigable α P R E) (hN : NoSteinerToSteiner R P E)
    (ζ : ℝ) (hζ : 0 < ζ) (q : Pt d) (j : ℕ) (x : ℕ → Pt d)
    (hwalk : IsBudgetedWalk E P q (searchBudget α (aspectRatio P) ζ) j x)
    (Cand : Finset (Pt d)) (hCand : IsCandidateSet E P R j x Cand)
    (y : Pt d) (hy : y ∈ Cand) (hymin : ∀ z ∈ Cand, dist y q ≤ dist z q) :
    (∀ p ∈ P, dist y q ≤ (approxConst α + ζ) * dist p q) ∧
      scanCount R (searchBudget α (aspectRatio P) ζ) j x ≤
        searchBudget α (aspectRatio P) ζ + 1 := by sorry

end SteinerNav.Supplement
