-- Prove2me | Theorems.Thm_SpatialSorting_counting_witnesses
-- name    : SpatialSorting.counting_witnesses
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:53:21.922729+00:00
-- url     : https://prove2.me/theorems/f8126c0b-4956-4fbd-be55-e0c785689554
-- title:
--   Lemma 7.4 — counting boundary-rooted witnesses
-- statement:
--   Let $q\ge2$, $A$ a cost matrix, $\delta\in(0,1]$, $L\ge0$ and $K\in\mathbb R$. The number of distinct families $\mathcal S(\sigma)$, $\sigma\in\Omega_{D_L}$, produced by the construction of Lemma 7.3 with cost $\mathcal H(\mathcal S(\sigma))\le K$ is at most
--
--   $$2\cdot72^{\lceil8L+2(1+\delta^{-1})K/A_{\min}\rceil}\,q^{2K/A_{\min}}.$$
--
--   The count is the entropy side of the energy–entropy comparison: it is exponential in $L+K$, while each witness of cost $K$ is suppressed by $e^{-c\beta K}$.
--
--   Differences from the source:
--   - encoding: ⌈8L + 2(1+δ⁻¹)K/A_min⌉ and K a cost → the natural-number ceiling ⌈·⌉₊ and any real K; reason: for K ≥ 0 the two ceilings agree; for K < 0 no family qualifies, since costs are nonnegative
--   - encoding: q^{2K/A_min} → the real power (q : ℝ)^(2K/A_min); reason: the exponent is real
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.4, p. 44 (PDF p. 45)

import Mathlib
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amin
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_cost
import Definitions.Def_SpatialSorting_bridgeFamily
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 7.4 — counting boundary-rooted witnesses.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.4, p. 44 (PDF p. 45).

Formalization Notes:
- encoding: ⌈8L + 2(1+δ⁻¹)K/A_min⌉ and K a cost → the natural-number ceiling ⌈·⌉₊ and any real K. For K ≥ 0 the two ceilings agree; for K < 0 no family qualifies, since costs are nonnegative.
- encoding: q^{2K/A_min} → the real power (q : ℝ)^(2K/A_min). The exponent is real. -/
theorem counting_witnesses {q : ℕ} [NeZero q] (hq : 2 ≤ q) (A : Matrix (Fin q) (Fin q) ℝ)
    (hA : IsCostMatrix A) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (L : ℕ) (K : ℝ) :
    ((((Finset.univ : Finset (Coloring q L)).image (bridgeFamily δ L)).filter
        (fun S => ∑ γ ∈ S, cost A γ ≤ K)).card : ℝ) ≤
      2 * (72 : ℝ) ^ ⌈8 * (L : ℝ) + 2 * (1 + δ⁻¹) * K / amin A⌉₊ *
        (q : ℝ) ^ (2 * K / amin A) := by sorry

end SpatialSorting
