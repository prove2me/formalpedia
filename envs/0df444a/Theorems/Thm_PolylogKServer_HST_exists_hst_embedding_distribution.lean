-- Prove2me | Theorems.Thm_PolylogKServer_HST_exists_hst_embedding_distribution
-- name    : PolylogKServer.HST.exists_hst_embedding_distribution
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-06T07:46:06.513288+00:00
-- url     : https://prove2.me/theorems/0c5d7957-b7c7-4a14-9e3e-9aae449b81da
-- title:
--   Every finite metric embeds into a distribution over dominating exact σ-HSTs with stretch O(σ log n / log σ)
-- statement:
--   There is a universal constant $C>0$ such that for every $\sigma\ge 2$ and every finite metric space $(M,d)$ with $n\ge 2$ points there is a probability distribution $(p_i)_{i\le r}$ over σ-HSTs $T_i$ (edge weights $L_i/\sigma^{j}$ at depth $j+1$) together with bijections $e_i$ of $M$ onto the leaves of $T_i$, such that every $T_i$ dominates $d$ and the expected stretch is $O(\sigma\log n/\log\sigma)$:
--
--   $$d(x,y)\le d_{T_i}(e_i x,e_i y),\qquad \sum_i p_i\, d_{T_i}(e_i x,e_i y)\le C\,\frac{\sigma\log n}{\log\sigma}\,d(x,y).$$
--
--   Role: the first step of the proof of Theorem 1: the general metric is replaced by a random σ-HST, on which Theorems 8, 6 and 7 are applied; the stretch factor enters the final competitive ratio.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, https://arxiv.org/abs/1110.1580v1, proof of Theorem 1, p. 9 (the embedding of M into a distribution over σ-HSTs, citing Fakcharoenphol–Rao–Talwar, A tight bound on approximating arbitrary metrics by tree metrics, J. Comput. Syst. Sci. 69 (2004), Theorem 2, in its base-σ form)

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree

namespace PolylogKServer.HST

theorem exists_hst_embedding_distribution :
  ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 2 ≤ σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M], 2 ≤ Fintype.card M →
        ∃ (r : ℕ) (p : Fin r → ℝ) (V : Fin r → Type) (_ : ∀ i, Fintype (V i))
          (_ : ∀ i, DecidableEq (V i)) (T : (i : Fin r) → WTree (V i))
          (e : (i : Fin r) → M ≃ (T i).Leaf),
          (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i, (T i).IsHST σ) ∧
          (∀ i (x y : M), dist x y ≤ (T i).treeDist (e i x) (e i y)) ∧
          ∀ x y : M, ∑ i, p i * (T i).treeDist (e i x) (e i y) ≤
            C * σ * Real.log (Fintype.card M) / Real.log σ * dist x y := by sorry

end PolylogKServer.HST
