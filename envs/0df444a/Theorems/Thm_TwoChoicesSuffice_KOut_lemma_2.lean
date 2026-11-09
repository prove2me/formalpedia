-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_lemma_2
-- name    : TwoChoicesSuffice.KOut.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:12.476787+00:00
-- url     : https://prove2.me/theorems/17495c8e-fb7d-454a-ba6a-2f46fcef0f29
-- title:
--   Lemma 2 — bridge potential is at most the component potential
-- statement:
--   Let $G$ be a finite simple graph and let $J\subseteq H\subseteq G$ be nested spanning subgraphs of $G$. Then
--   $$
--   \Psi_G(J,H)\le\Phi_G(J),
--   $$
--   where $\Psi_G(J,H)$ sums $\min\{\deg_G(u),\deg_G(v)\}$ over the bridges $uv$ of $H$ outside $J$, and $\Phi_G(J)$ sums the maximum original degree over the components of $J$.
--
--   This deterministic inequality converts the count of inverse switchings, which are indexed by bridges, into a component potential.
--
--   Differences from the source: none.
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Lemma 2, printed p. 7, PDF p. 8

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling
import Definitions.Def_TwoChoicesSuffice_KOut_Potentials

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Lemma 2 (PDF p. 8, printed p. 7). For nested spanning subgraphs `J ≤ H ≤ G` of a simple
graph `G`, the bridge potential is at most the max-degree component potential:
`Ψ_G(J, H) ≤ Φ_G(J)`. -/
theorem lemma_2 {V : Type*} [Fintype V] (G J H : SimpleGraph V) (hJH : J ≤ H) (hHG : H ≤ G) :
    bridgePotential G J H ≤ degPotential G J := by sorry

end TwoChoicesSuffice.KOut
