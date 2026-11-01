-- Prove2me | Theorems.Thm_ToricMemory_eq_49
-- name    : ToricMemory.eq_49
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:38.054986+00:00
-- url     : https://prove2.me/theorems/b2c83813-43ba-4a87-a037-e7878b7c1e9c
-- title:
--   Eq. (49) — the minimal chain is at least as likely as its swap along a cycle
-- statement:
--   Let $p,q\in[0,1]$, let $D$ be a maximum-likelihood decoder, let $E$ be an error history with $\mu_{p,q}(E)>0$ and $E_{\min}=D(\partial E)$, and let $P$ be a cycle ($\partial P=\emptyset$) contained in $E+E_{\min}$. Write $e=P\cap E$ and $m=P\cap E_{\min}$, and $p_\ell\in\{p,q\}$ for the error probability of the link $\ell$. Then
--   $$
--   \prod_{\ell\in e}p_\ell\prod_{\ell\in m}(1-p_\ell)\;\le\;\prod_{\ell\in m}p_\ell\prod_{\ell\in e}(1-p_\ell).
--   $$
--   For $0<p,q<1$ this is eq. (49): $\big(\tfrac{p}{1-p}\big)^{H_e}\big(\tfrac{q}{1-q}\big)^{V_e}\le\big(\tfrac{p}{1-p}\big)^{H_m}\big(\tfrac{q}{1-q}\big)^{V_m}$, where $H_e,V_e$ and $H_m,V_m$ count the horizontal and vertical links of $e$ and $m$.
--
--   The inequality says that the decoder's choice along $P$ is at least as likely as the actual errors along $P$; it is the first step of the Peierls-type bound on the failure probability.
--
--   Differences from the source:
--   - generalization: a particular cycle of the spacetime lattice with H horizontal and V vertical links (a connected path) → any chain P with empty boundary contained in E Δ E_min; reason: the swap argument uses only ∂P = ∅; every closed path is such a chain
--   - generalization: E_min, the chain of maximal probability (44)–(46) with the observed boundary, ties broken randomly (p. 18), for error probabilities p, q → every map D returning, for each achievable boundary, a chain of maximal chainProb p q with that boundary (IsMLDecoder), for all p, q ∈ [0, 1]; reason: a random tie-break independent of E is a mixture of such maps, so the statement for every D specializes to the paper's decoder; chainProb has the same argmax as (44) for 0 < p, q < 1
--   - encoding: eq. (49) in the ratio form (p/(1−p))^H_e (q/(1−q))^V_e … → the inequality multiplied through by ∏_{ℓ∈P}(1 − p_ℓ), as products over e = P ∩ E and m = P ∩ E_min; reason: equivalent for 0 ≤ p, q < 1 and defined at p = 1 or q = 1
--   - encoding: E an error history (one that occurs) → hypothesis 0 < chainProb p q E; reason: excludes only histories of probability 0; it holds for every E when 0 < p, q < 1
--   - reading: a spacetime lattice of L×L sites over T time slices, with L²T sites, 2L²T horizontal and L²T vertical links (Sec. V B–C, pp. 19–20) → the 3-torus ZMod L × ZMod L × ZMod T with periodic time; links are (site, direction) pairs; reason: the counts printed on p. 20 are exactly those of the 3-torus; an open-time slab has L²(T−1) vertical links
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V B, eq. (49), p. 19

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_IsMLDecoder

open Finset

namespace ToricMemory

/-- **Eq. (49)**, Dennis–Kitaev–Landahl–Preskill, arXiv:quant-ph/0110143v1, Sec. V B, p. 19
(PDF p. 19): "our procedure for constructing `E_min` ensures that
`(p/(1−p))^{H_e}(q/(1−q))^{V_e} ≤ (p/(1−p))^{H_m}(q/(1−q))^{V_m}`". Let `E` be an error history
that occurs (`chainProb p q E > 0`), `E_min = D(∂E)` its maximum-likelihood decoding, and `P` a
cycle contained in `E + E_min`; write `e = P ∩ E` and `m = P ∩ E_min`. Then
`∏_{ℓ∈e} p_ℓ · ∏_{ℓ∈m} (1 − p_ℓ) ≤ ∏_{ℓ∈m} p_ℓ · ∏_{ℓ∈e} (1 − p_ℓ)`.

**Formalization Note** This is (49) multiplied through by `∏_{ℓ∈P} (1 − p_ℓ)`; for `0 ≤ p, q < 1`
it is equivalent to (49), and it stays defined at `p = 1` or `q = 1`. `P` is any cycle
(empty boundary), not only a self-avoiding one. -/
theorem eq_49 {L T : ℕ} [NeZero L] [NeZero T] (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (D : Finset (Site L T) → Finset (Link L T))
    (hD : IsMLDecoder p q D) (E : Finset (Link L T)) (hE : 0 < chainProb p q E)
    (P : Finset (Link L T)) (hP : boundary P = ∅) (hPE : P ⊆ symmDiff E (D (boundary E))) :
    (∏ ℓ ∈ P ∩ E, linkProb p q ℓ) * (∏ ℓ ∈ P ∩ D (boundary E), (1 - linkProb p q ℓ)) ≤
      (∏ ℓ ∈ P ∩ D (boundary E), linkProb p q ℓ) * (∏ ℓ ∈ P ∩ E, (1 - linkProb p q ℓ)) := by sorry

end ToricMemory
