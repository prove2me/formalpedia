-- Prove2me | Theorems.Thm_SatiationFisherNSW_lemma_4_1
-- name    : SatiationFisherNSW.lemma_4_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:25:44.316114+00:00
-- url     : https://prove2.me/theorems/a6ad61da-65c1-4f0e-89e2-feccbcaea726
-- title:
--   Lemma 4.1 — truncating values at the caps does not change integral valuations
-- statement:
--   Let $v_{ij}\ge0$, $c_i>0$ be an instance of Nash social welfare with budget-additive valuations, and let $v'_{ij}=\min(v_{ij},c_i)$. For every integral allocation $S$ and every agent $i$,
--   $$
--   v'_i(S)=\min\Bigl(c_i,\sum_{j\in S_i}v'_{ij}\Bigr)=\min\Bigl(c_i,\sum_{j\in S_i}v_{ij}\Bigr)=v_i(S).
--   $$
--
--   This justifies assuming $v_{ij}\le c_i$ throughout §4.1.
--
--   Differences from the source:
--   - encoding: an integral allocation $S=(S_1,\dots,S_n)$ with characteristic vector $x^S$ (p.7) → a map $S:G\to$ `Option B` giving each item to at most one agent; reason: valuations are monotone, so allowing unassigned items changes no maximum and no bound
-- source:
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, Lemma 4.1, p.23

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
open scoped Classical

namespace SatiationFisherNSW

/-- Lemma 4.1 (Garg, Hoefer, Mehlhorn, arXiv:1707.04428v3, p.23): truncating the values at the
caps, `v'_{ij} = min(v_{ij}, c_i)`, does not change the valuation of any integral allocation:
`v'_i(x) = v_i(x)`.

**Formalization Note** An integral allocation is `S : G → Option B` (each item to at most one
agent), and `v'_i(x^S_i) = min(c_i, Σ_{j∈S_i} v'_{ij})`. -/
theorem lemma_4_1 {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (S : G → Option B) (i : B) :
    min (I.c i) (∑ j ∈ Finset.univ.filter (fun j => S j = some i), min (I.v i j) (I.c i)) =
      I.val i S := by sorry

end SatiationFisherNSW
