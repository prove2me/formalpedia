-- Prove2me | Theorems.Thm_ToricMemory_eq_50
-- name    : ToricMemory.eq_50
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:58.504549+00:00
-- url     : https://prove2.me/theorems/efe4f1e5-e8a8-4e13-bcaa-5835defc8b3b
-- title:
--   Eq. (50) — errors on a cycle of $E+E_{\min}$ carry at most half its weight
-- statement:
--   With $p,q\in[0,1]$, a maximum-likelihood decoder $D$, an error history $E$ with $\mu_{p,q}(E)>0$, $E_{\min}=D(\partial E)$, a cycle $P\subseteq E+E_{\min}$, $e=P\cap E$ and $m=P\cap E_{\min}$ as in (49):
--   $$
--   \prod_{\ell\in e}p_\ell\prod_{\ell\in m}(1-p_\ell)\;\le\;\prod_{\ell\in P}\sqrt{p_\ell(1-p_\ell)}.
--   $$
--   For $0<p,q<1$ this is eq. (50): $\big(\tfrac{p}{1-p}\big)^{H_e}\big(\tfrac{q}{1-q}\big)^{V_e}\le\Big[\big(\tfrac{p}{1-p}\big)^{H}\big(\tfrac{q}{1-q}\big)^{V}\Big]^{1/2}$, where $P$ has $H$ horizontal and $V$ vertical links.
--
--   It bounds the probability of each admissible error pattern on $P$, which (52) then sums over the $2^{H+V}$ patterns.
--
--   Differences from the source:
--   - generalization: a particular cycle of the spacetime lattice with H horizontal and V vertical links (a connected path) → any chain P with empty boundary contained in E Δ E_min; reason: the swap argument uses only ∂P = ∅; every closed path is such a chain
--   - generalization: E_min, the chain of maximal probability (44)–(46) with the observed boundary, ties broken randomly (p. 18), for error probabilities p, q → every map D returning, for each achievable boundary, a chain of maximal chainProb p q with that boundary (IsMLDecoder), for all p, q ∈ [0, 1]; reason: a random tie-break independent of E is a mixture of such maps, so the statement for every D specializes to the paper's decoder; chainProb has the same argmax as (44) for 0 < p, q < 1
--   - encoding: eq. (50) in the ratio form (p/(1−p))^H_e (q/(1−q))^V_e … → the inequality multiplied through by ∏_{ℓ∈P}(1 − p_ℓ), as products over e = P ∩ E and m = P ∩ E_min; reason: equivalent for 0 ≤ p, q < 1 and defined at p = 1 or q = 1
--   - encoding: E an error history (one that occurs) → hypothesis 0 < chainProb p q E; reason: excludes only histories of probability 0; it holds for every E when 0 < p, q < 1
--   - reading: a spacetime lattice of L×L sites over T time slices, with L²T sites, 2L²T horizontal and L²T vertical links (Sec. V B–C, pp. 19–20) → the 3-torus ZMod L × ZMod L × ZMod T with periodic time; links are (site, direction) pairs; reason: the counts printed on p. 20 are exactly those of the 3-torus; an open-time slab has L²(T−1) vertical links
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V B, eq. (50), p. 19

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_IsMLDecoder

open Finset

namespace ToricMemory

/-- **Eq. (50)**, arXiv:quant-ph/0110143v1, Sec. V B, p. 19 (PDF p. 19): "Combining the
inequalities eq. (48) and eq. (49) we obtain
`(p/(1−p))^{H_e}(q/(1−q))^{V_e} ≤ [(p/(1−p))^H (q/(1−q))^V]^{1/2}`". With `E`, `E_min = D(∂E)`,
the cycle `P ⊆ E + E_min`, `e = P ∩ E` and `m = P ∩ E_min` as in (49):
`∏_{ℓ∈e} p_ℓ · ∏_{ℓ∈m} (1 − p_ℓ) ≤ ∏_{ℓ∈P} √(p_ℓ(1 − p_ℓ))`.

**Formalization Note** This is (50) multiplied through by `∏_{ℓ∈P} (1 − p_ℓ)` (since `P` is the
disjoint union of `e` and `m`); it stays defined at `p = 1` or `q = 1`. -/
theorem eq_50 {L T : ℕ} [NeZero L] [NeZero T] (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (D : Finset (Site L T) → Finset (Link L T))
    (hD : IsMLDecoder p q D) (E : Finset (Link L T)) (hE : 0 < chainProb p q E)
    (P : Finset (Link L T)) (hP : boundary P = ∅) (hPE : P ⊆ symmDiff E (D (boundary E))) :
    (∏ ℓ ∈ P ∩ E, linkProb p q ℓ) * (∏ ℓ ∈ P ∩ D (boundary E), (1 - linkProb p q ℓ)) ≤
      ∏ ℓ ∈ P, Real.sqrt (linkProb p q ℓ * (1 - linkProb p q ℓ)) := by sorry

end ToricMemory
