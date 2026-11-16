-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_Supplement_rounding_reduction
-- name    : PlanarMetricElections.Peer.Supplement.rounding_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:43:56.182209+00:00
-- url     : https://prove2.me/theorems/b1ddda9a-0d34-4849-b8ec-941b3e1ba0c8
-- title:
--   Lemma 5.4 — nearest-candidate rounding: $\mathrm{RR}_{\ell_2}(k)\le\varepsilon_k$ on $\mathbb R^r$
-- statement:
--   For all positive integers $r$ and $k$, the restricted Euclidean election factor on $\mathbb R^r$ is at most the weak convex net factor on $\mathbb R^r$:
--
--   $$\mathrm{RR}_{\ell_2}(k)\le\varepsilon_k .$$
--
--   Here $\mathrm{RR}_{\ell_2}(k)$ is the worst case, over all Euclidean elections $(V,C)$ on $\mathbb R^r$ (nonempty finite voters and candidates, no voter equidistant from two distinct candidates), of the best guarantee a coalition $S\subseteq C$ of $1$ to $k$ candidates achieves against a challenger $c\in C$, measured by the fraction of voters strictly closer to $c$ than to every member of $S$; and $\varepsilon_k$ is the worst case, over nonempty finite $P\subseteq\mathbb R^r$, of the smallest uncovered mass $\sup\{|K\cap P|/|P|: K \text{ convex},\ K\cap Q=\emptyset\}$ achievable by a set $Q$ of at most $k$ arbitrary points.
--
--   Every upper bound for weak convex nets therefore transfers to Condorcet-winning sets in Euclidean metric elections of the same dimension.
--
--   Differences from the source: none.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Lemma 5.4, p. 10 (PDF p. 11)

import Definitions.Def_PlanarMetricElections_Peer_Supplement_WeakNet
import Definitions.Def_PlanarMetricElections_Peer_Supplement_RestrictedElection

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer.Supplement

theorem rounding_reduction (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    restrictedFactor r k ≤ weakNetFactor r k := by sorry

end PlanarMetricElections.Peer.Supplement
