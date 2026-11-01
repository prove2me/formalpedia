-- Prove2me | Theorems.Thm_ToricMemory_eq_55
-- name    : ToricMemory.eq_55
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:08.486988+00:00
-- url     : https://prove2.me/theorems/62a2d26a-56f7-42e3-809c-49bc76e6bdc4
-- title:
--   Eq. (55) — $\mathrm{Prob}_{\rm fail}\le\sum_V\sum_{H\ge L}\mathrm{Prob}_{\rm SAP}(H,V)\le L^2T\sum_V\sum_{H\ge L}n_{\rm SAP}(H,V)(4\tilde p)^{H/2}(4\tilde q)^{V/2}$
-- statement:
--   Let $p,q\in[0,1]$, $\tilde p=p(1-p)$, $\tilde q=q(1-q)$, and let $D$ be a maximum-likelihood decoder on the $L\times L\times T$ lattice. Then
--   $$
--   \mathrm{Prob}_{\rm fail}\;\le\;\sum_{V=0}^{L^2T}\sum_{H=L}^{2L^2T}\mathrm{Prob}_{\rm SAP}(H,V)\;\le\;L^2T\sum_{V=0}^{L^2T}\sum_{H=L}^{2L^2T}n_{\rm SAP}(H,V)\,(4\tilde p)^{H/2}(4\tilde q)^{V/2}.
--   $$
--
--   Combined with a bound on $n_{\rm SAP}$, this reduces the failure probability to a counting problem for self-avoiding polygons.
--
--   Differences from the source:
--   - reading: E + E_min contains homologically nontrivial paths (p. 20) → E Δ E_min contains a cycle (empty boundary) with odd x-winding or odd y-winding (Fails); reason: on the 3-torus a cycle winding only in time has no horizontal link, while p. 20 says a damaging path has at least L horizontal links; the event contains the event that the class of E Δ E_min is nontrivial
--   - generalization: E_min, the chain of maximal probability (44)–(46) with the observed boundary, ties broken randomly (p. 18), for error probabilities p, q → every map D returning, for each achievable boundary, a chain of maximal chainProb p q with that boundary (IsMLDecoder), for all p, q ∈ [0, 1]; reason: a random tie-break independent of E is a mixture of such maps, so the statement for every D specializes to the paper's decoder; chainProb has the same argmax as (44) for 0 < p, q < 1
--   - encoding: Σ_V Σ_{H≥L} (unbounded ranges) → V from 0 to L²T and H from L to 2L²T; reason: there are L²T vertical and 2L²T horizontal links (p. 20), so every term outside these ranges is 0
--   - encoding: (4p̃), (4q̃)^{·/2} powers → (√x)^n for x^{n/2}; reason: the same real number for x ≥ 0; avoids ℕ division in the exponent
--   - encoding: n_SAP(H, V) with a specified starting site → sapTorus L T 0 H V; reason: the count does not depend on the starting site (vertex-transitivity)
--   - reading: a spacetime lattice of L×L sites over T time slices, with L²T sites, 2L²T horizontal and L²T vertical links (Sec. V B–C, pp. 19–20) → the 3-torus ZMod L × ZMod L × ZMod T with periodic time; links are (site, direction) pairs; reason: the counts printed on p. 20 are exactly those of the 3-torus; an open-time slab has L²(T−1) vertical links
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V B, eq. (55), p. 20

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_IsMLDecoder
import Definitions.Def_ToricMemory_Failure
import Definitions.Def_ToricMemory_TorusSAP
import Definitions.Def_ToricMemory_probSAP

open Finset

namespace ToricMemory

/-- **Eq. (55)**, arXiv:quant-ph/0110143v1, Sec. V B, p. 20 (PDF p. 20): "Hence we can bound
the failure probability as
`Prob_fail ≤ Σ_V Σ_{H≥L} Prob_SAP(H, V) ≤ L²T Σ_V Σ_{H≥L} n_SAP(H, V) · (4p̃)^{H/2}(4q̃)^{V/2}`."
Both inequalities, for every maximum-likelihood decoder `D`, with `V` from `0` to `L²T` and `H`
from `L` to `2L²T`.

**Formalization Note** The ranges of `H` and `V` are cut at the numbers `2L²T` and `L²T` of
horizontal and vertical links on the lattice (p. 20), beyond which `Prob_SAP(H, V)` and
`n_SAP(H, V)` vanish; `(4p̃)^{H/2}` is written `(√(4p̃))^H`. `n_SAP(H, V)` is counted at the
starting site `0`. -/
theorem eq_55 {L T : ℕ} [NeZero L] [NeZero T] (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (D : Finset (Site L T) → Finset (Link L T))
    (hD : IsMLDecoder p q D) :
    probFail p q D ≤
        ∑ V ∈ range (L ^ 2 * T + 1), ∑ H ∈ Icc L (2 * L ^ 2 * T), probSAP p q D H V ∧
      ∑ V ∈ range (L ^ 2 * T + 1), ∑ H ∈ Icc L (2 * L ^ 2 * T), probSAP p q D H V ≤
        (L : ℝ) ^ 2 * T * ∑ V ∈ range (L ^ 2 * T + 1), ∑ H ∈ Icc L (2 * L ^ 2 * T),
          (sapTorus L T 0 H V : ℝ) * Real.sqrt (4 * (p * (1 - p))) ^ H *
            Real.sqrt (4 * (q * (1 - q))) ^ V := by sorry

end ToricMemory
