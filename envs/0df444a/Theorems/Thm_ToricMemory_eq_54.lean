-- Prove2me | Theorems.Thm_ToricMemory_eq_54
-- name    : ToricMemory.eq_54
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:54.274983+00:00
-- url     : https://prove2.me/theorems/1f7b4c39-9cf0-452f-99dc-e67bbf5f3dc0
-- title:
--   Eq. (54) — $\mathrm{Prob}_{\rm SAP}(H,V)\le L^2T\,n_{\rm SAP}(H,V)\,2^{H+V}(\tilde p^H\tilde q^V)^{1/2}$
-- statement:
--   Let $p,q\in[0,1]$, $\tilde p=p(1-p)$, $\tilde q=q(1-q)$, and let $D$ be a maximum-likelihood decoder. For all $H,V\ge0$, the probability that $E+E_{\min}$ contains some self-avoiding polygon with $H$ horizontal and $V$ vertical links satisfies
--   $$
--   \mathrm{Prob}_{\rm SAP}(H,V)\;\le\;L^2T\cdot n_{\rm SAP}(H,V)\cdot2^{H+V}\big(\tilde p^{H}\tilde q^{V}\big)^{1/2},
--   $$
--   where $n_{\rm SAP}(H,V)$ is the number of such polygons with a specified starting site.
--
--   The paper calls this bound "the foundation of the results that follow".
--
--   Differences from the source:
--   - generalization: E_min, the chain of maximal probability (44)–(46) with the observed boundary, ties broken randomly (p. 18), for error probabilities p, q → every map D returning, for each achievable boundary, a chain of maximal chainProb p q with that boundary (IsMLDecoder), for all p, q ∈ [0, 1]; reason: a random tie-break independent of E is a mixture of such maps, so the statement for every D specializes to the paper's decoder; chainProb has the same argmax as (44) for 0 < p, q < 1
--   - encoding: n_SAP(H, V) with a specified starting site → sapTorus L T 0 H V, the count at the site 0; reason: the torus is vertex-transitive, so the count does not depend on the starting site
--   - reading: a spacetime lattice of L×L sites over T time slices, with L²T sites, 2L²T horizontal and L²T vertical links (Sec. V B–C, pp. 19–20) → the 3-torus ZMod L × ZMod L × ZMod T with periodic time; links are (site, direction) pairs; reason: the counts printed on p. 20 are exactly those of the 3-torus; an open-time slab has L²(T−1) vertical links
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V B, eq. (54), p. 19

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_IsMLDecoder
import Definitions.Def_ToricMemory_TorusSAP
import Definitions.Def_ToricMemory_probSAP

namespace ToricMemory

/-- **Eq. (54)**, arXiv:quant-ph/0110143v1, Sec. V B, p. 19 (PDF p. 19): "If `n_SAP(H, V)`
denotes the number of SAP's with `(H, V)` links and a specified starting site, then the
probability `Prob_SAP(H, V)` that `E + E_min` contains any SAP with `(H, V)` links satisfies
`Prob_SAP(H, V) ≤ L²T · n_SAP(H, V) · 2^{H+V}(p̃^H q̃^V)^{1/2}`", with `p̃ = p(1 − p)`,
`q̃ = q(1 − q)`, for every maximum-likelihood decoder `D`.

**Formalization Note** `n_SAP(H, V)` is the count `sapTorus L T 0 H V` at the starting site
`0`; by translation invariance of the torus it is the same at every site. -/
theorem eq_54 {L T : ℕ} [NeZero L] [NeZero T] (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (D : Finset (Site L T) → Finset (Link L T))
    (hD : IsMLDecoder p q D) (H V : ℕ) :
    probSAP p q D H V ≤
      (L : ℝ) ^ 2 * T * sapTorus L T 0 H V * 2 ^ (H + V) *
        Real.sqrt ((p * (1 - p)) ^ H * (q * (1 - q)) ^ V) := by sorry

end ToricMemory
