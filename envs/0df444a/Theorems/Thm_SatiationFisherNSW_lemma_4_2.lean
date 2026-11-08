-- Prove2me | Theorems.Thm_SatiationFisherNSW_lemma_4_2
-- name    : SatiationFisherNSW.lemma_4_2
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:25:54.074236+00:00
-- url     : https://prove2.me/theorems/e2898337-e68a-4074-bc7a-72b86638e26e
-- title:
--   Lemma 4.2 — without money clearing the optimal Nash social welfare is $0$
-- statement:
--   Consider the Fisher market $\mathcal M$ of an instance of Nash social welfare ($u_{ij}=\min(v_{ij},c_i)$, $m_i=d_j=1$). If $\mathcal M$ is not money clearing, then the maximum Nash social welfare for indivisible items is $0$: every integral allocation $S$ satisfies
--   $$
--   \prod_{i\in B}v_i(S)=0 .
--   $$
--
--   This is why the rest of §4.1 may assume money clearing.
--
--   Differences from the source:
--   - encoding: an integral allocation $S=(S_1,\dots,S_n)$ with characteristic vector $x^S$ (p.7) → a map $S:G\to$ `Option B` giving each item to at most one agent; reason: valuations are monotone, so allowing unassigned items changes no maximum and no bound
--   - encoding: "the maximum Nash social welfare … is 0" → every integral allocation has $\prod_i v_i(S)=0$; reason: the geometric mean of nonnegative numbers is $0$ exactly when their product is, and there are finitely many allocations
-- source:
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, Lemma 4.2, p.23

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
open scoped Classical

namespace SatiationFisherNSW

/-- Lemma 4.2 (Garg, Hoefer, Mehlhorn, arXiv:1707.04428v3, p.23): if the Fisher market `M` of an
instance of the Nash social welfare problem is not money clearing, then the maximum Nash social
welfare for indivisible items is `0`, i.e. every integral allocation has `∏_i v_i(x^S_i) = 0`.

**Formalization Note** "The maximum Nash social welfare is 0" is stated as: the product of the
valuations of every integral allocation `S : G → Option B` is `0` (the geometric mean is `0`
exactly when the product is). -/
theorem lemma_4_2 {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hMC : ¬ I.market.IsMoneyClearing) (S : G → Option B) :
    ∏ i, I.val i S = 0 := by sorry

end SatiationFisherNSW
