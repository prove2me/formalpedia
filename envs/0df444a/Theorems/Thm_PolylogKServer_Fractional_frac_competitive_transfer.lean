-- Prove2me | Theorems.Thm_PolylogKServer_Fractional_frac_competitive_transfer
-- name    : PolylogKServer.Fractional.frac_competitive_transfer
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-06T07:46:46.56979+00:00
-- url     : https://prove2.me/theorems/8651eb05-1409-4a41-b8f6-bbefdfbcc0eb
-- title:
--   A competitive fractional k-server algorithm transfers between trees whose leaf metrics agree up to a factor c₁
-- statement:
--   Let $T$ and $T'$ be weighted trees with leaf metrics $M$ and $M'$, and let $g:M\to M'$ be a bijection with
--
--   $$d'(gx,gy)\le d(x,y)\le c_1\,d'(gx,gy)\qquad(x,y\in M).$$
--
--   If a fractional k-server algorithm on $T'$ is $c_2$-competitive from $g\circ C_0$ ($c_1,c_2\ge 0$), then there is a fractional k-server algorithm on $T$ that is $c_1c_2$-competitive from $C_0$.
--
--   Role: in the proof of Theorem 1 the fractional algorithm is built on the shallow weighted HST $T'$ of Theorem 8 and must be carried back to the σ-HST $T$, whose leaf distances are within the factor $2\sigma/(\sigma-1)$ of those of $T'$.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, https://arxiv.org/abs/1110.1580v1, proof of Theorem 1, p. 9 (transfer of the fractional algorithm from the weighted HST T' of Theorem 8 back to the σ-HST T, whose leaf distances agree up to the factor 2σ/(σ−1))

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PolylogKServer_Fractional_KServer
open PolylogKServer.HST

namespace PolylogKServer.Fractional

theorem frac_competitive_transfer :
  ∀ {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (T : WTree V) (T' : WTree V') (k : ℕ)
    (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf), T.IsLeafMetric M e →
    ∀ (M' : Type) [MetricSpace M'] [Fintype M'] (e' : M' ≃ T'.Leaf), T'.IsLeafMetric M' e' →
    ∀ (g : M ≃ M') (c₁ c₂ : ℝ), 0 ≤ c₁ →
    (∀ x y : M, dist (g x) (g y) ≤ dist x y) →
    (∀ x y : M, dist x y ≤ c₁ * dist (g x) (g y)) →
    ∀ (C₀ : KServer.Config k M) (F : FracKServerAlg k M'),
    F.IsCompetitiveFrom T' e' (fun j => g (C₀ j)) c₂ → 0 ≤ c₂ →
    ∃ F' : FracKServerAlg k M, F'.IsCompetitiveFrom T e C₀ (c₁ * c₂) := by sorry

end PolylogKServer.Fractional
