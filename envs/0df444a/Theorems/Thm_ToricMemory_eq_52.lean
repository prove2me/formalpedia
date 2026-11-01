-- Prove2me | Theorems.Thm_ToricMemory_eq_52
-- name    : ToricMemory.eq_52
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:29.275877+00:00
-- url     : https://prove2.me/theorems/fd27349e-0f9c-4780-abf6-17ddd55ff8ec
-- title:
--   Eqs. (52)–(53) — a given cycle lies in $E+E_{\min}$ with probability $\le 2^{H+V}(\tilde p^H\tilde q^V)^{1/2}$ (corrected: cycles only)
-- statement:
--   Let $p,q\in[0,1]$, $\tilde p=p(1-p)$ and $\tilde q=q(1-q)$, and let $D$ be a maximum-likelihood decoder. For every cycle $P$ ($\partial P=\emptyset$) with $H$ horizontal and $V$ vertical links, the probability that $E+E_{\min}$ contains $P$, where $E\sim\mu_{p,q}$ and $E_{\min}=D(\partial E)$, satisfies
--   $$
--   \mathrm{Prob}(H,V)=\sum_{E}\mu_{p,q}(E)\,\mathbf 1\big[P\subseteq E+E_{\min}\big]\;\le\;2^{H+V}\big(\tilde p^{H}\tilde q^{V}\big)^{1/2}.
--   $$
--
--   This is the single-cycle estimate behind the union bound (54).
--
--   Differences from the source:
--   - correction: the bound for any connected path, whether or not the path is closed (pp. 18–19) → the bound for cycles (∂P = ∅) only; reason: for an open path the e and m links do not share a boundary and the bound fails: p = 1/2, q = 10⁻³, L = T = 10, P a single vertical link, with the ML decoder that places its one vertical link per layer of odd parity on P, gives probability ≈ 0.089 > 2√(q(1−q)) ≈ 0.063 (paper.md C2); only cycles are used from (54) on
--   - generalization: a particular cycle (a connected closed path) → any chain P with empty boundary; reason: the derivation uses only ∂P = ∅; every closed path is such a chain
--   - generalization: E_min, the chain of maximal probability (44)–(46) with the observed boundary, ties broken randomly (p. 18), for error probabilities p, q → every map D returning, for each achievable boundary, a chain of maximal chainProb p q with that boundary (IsMLDecoder), for all p, q ∈ [0, 1]; reason: a random tie-break independent of E is a mixture of such maps, so the statement for every D specializes to the paper's decoder; chainProb has the same argmax as (44) for 0 < p, q < 1
--   - reading: a spacetime lattice of L×L sites over T time slices, with L²T sites, 2L²T horizontal and L²T vertical links (Sec. V B–C, pp. 19–20) → the 3-torus ZMod L × ZMod L × ZMod T with periodic time; links are (site, direction) pairs; reason: the counts printed on p. 20 are exactly those of the 3-torus; an open-time slab has L²(T−1) vertical links
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V B, eqs. (51)–(53), p. 19

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_IsMLDecoder

open Finset

namespace ToricMemory

/-- **Eq. (52)–(53)**, arXiv:quant-ph/0110143v1, Sec. V B, p. 19 (PDF p. 19): for a particular
cycle `P` with `H` horizontal and `V` vertical links, the probability `Prob(H, V)` that
`E + E_min` contains `P` satisfies `Prob(H, V) ≤ 2^{H+V}(p̃^H q̃^V)^{1/2}`, where
`p̃ = p(1 − p)` and `q̃ = q(1 − q)`. Here `E` is drawn from `chainProb p q` and
`E_min = D(∂E)` for any maximum-likelihood decoder `D`.

**Formalization Note** Stated for cycles (`∂P = ∅`) only: the paper's aside that the bound
holds for open paths as well (pp. 18–19) is false for some maximum-likelihood tie-breaks, and
only cycles are used afterwards. -/
theorem eq_52 {L T : ℕ} [NeZero L] [NeZero T] (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (D : Finset (Site L T) → Finset (Link L T))
    (hD : IsMLDecoder p q D) (P : Finset (Link L T)) (hP : boundary P = ∅) :
    (∑ E : Finset (Link L T),
        if P ⊆ symmDiff E (D (boundary E)) then chainProb p q E else 0) ≤
      2 ^ (hCount P + vCount P) *
        Real.sqrt ((p * (1 - p)) ^ hCount P * (q * (1 - q)) ^ vCount P) := by sorry

end ToricMemory
