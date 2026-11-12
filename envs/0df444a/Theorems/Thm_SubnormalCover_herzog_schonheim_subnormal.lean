-- Prove2me | Theorems.Thm_SubnormalCover_herzog_schonheim_subnormal
-- name    : SubnormalCover.herzog_schonheim_subnormal
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:47:43.011799+00:00
-- url     : https://prove2.me/theorems/0e164d0b-ba7a-451b-ad33-404926dafde4
-- title:
--   Herzog-Schönheim conjecture for subnormal uniform covers
-- statement:
--   **The Herzog--Sch\"onheim conjecture for subnormal uniform covers.** In 1974 Herzog and Sch\"onheim conjectured that if the left cosets $a_1G_1,\dots,a_kG_k$ ($k>1$) partition a group $G$ then the finite indices $[G:G_1],\dots,[G:G_k]$ cannot be pairwise distinct. Sun proves the conjecture, in the stronger setting of uniform covers (each $x\in G$ covered exactly $w$ times, $w\ge1$ arbitrary), whenever the $G_i$ are subnormal of finite index and not all equal to $G$: two of the indices must coincide.
--
--   *Formalization note.* The conclusion asserts distinct **indices into the family**, $i\ne j$ in $\texttt{Fin }k$, so it says two distinct parts of the cover have equal index; the subgroups $K_i$ and $K_j$ themselves may well be equal, which is the usual reading of the conjecture. Nontriviality is `∃ i, K i ≠ ⊤`, which together with the uniform-cover hypothesis already forces $k\ge 2$, so no separate $1<k$ assumption appears.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Corollary 4.2 (specialised to $p = $ largest prime divisor of $N$) and Theorem 1.1, 'the indices cannot be pairwise distinct'; abstract, Herzog--Schönheim Conjecture in §1

import Mathlib
import Definitions.Def_SubnormalCover_uniformCover

namespace SubnormalCover

theorem herzog_schonheim_subnormal {G : Type*} [Group G] {k : ℕ}
    (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ) (hcov : IsUniformCover K a w)
    (hfin : ∀ i, (K i).FiniteIndex) (hsn : ∀ i, (K i).IsSubnormal) (hnt : ∃ i, K i ≠ ⊤) :
    ∃ i j : Fin k, i ≠ j ∧ (K i).index = (K j).index := by
  sorry

end SubnormalCover
