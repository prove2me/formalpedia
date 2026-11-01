-- Prove2me | Theorems.Thm_ToricMemory_eq_59
-- name    : ToricMemory.eq_59
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:46.097253+00:00
-- url     : https://prove2.me/theorems/90599c0f-5938-4ee9-854e-6ed847cd31c4
-- title:
--   Eq. (59) — $\mathrm{Prob}_{\rm fail}\le L^2T\sum_V\sum_{H\ge L}P_3(H+V)(4\mu_3^2\tilde p)^{H/2}(4\mu_3^2\tilde q)^{V/2}$
-- statement:
--   There are a constant $C$ and an integer $k\ge0$ such that for all $L,T\ge1$, all $p,q\in[0,1]$ and every maximum-likelihood decoder on the $L\times L\times T$ lattice,
--   $$
--   \mathrm{Prob}_{\rm fail}\;\le\;L^2T\sum_{V=0}^{L^2T}\sum_{H=L}^{2L^2T}C(H+V+1)^k\,(4\mu_3^2\tilde p)^{H/2}(4\mu_3^2\tilde q)^{V/2},
--   $$
--   where $\tilde p=p(1-p)$ and $\tilde q=q(1-q)$.
--
--   Below the threshold (60) each term is at most $(4\mu_3^2\tilde p)^{L/2}$, which gives (62).
--
--   Differences from the source:
--   - reading: E + E_min contains homologically nontrivial paths (p. 20) → E Δ E_min contains a cycle (empty boundary) with odd x-winding or odd y-winding (Fails); reason: on the 3-torus a cycle winding only in time has no horizontal link, while p. 20 says a damaging path has at least L horizontal links; the event contains the event that the class of E Δ E_min is nontrivial
--   - generalization: E_min, the chain of maximal probability (44)–(46) with the observed boundary, ties broken randomly (p. 18), for error probabilities p, q → every map D returning, for each achievable boundary, a chain of maximal chainProb p q with that boundary (IsMLDecoder), for all p, q ∈ [0, 1]; reason: a random tie-break independent of E is a mixture of such maps, so the statement for every D specializes to the paper's decoder; chainProb has the same argmax as (44) for 0 < p, q < 1
--   - reading: μ₃ ≈ 4.684 (eq. (58)) → mu3 := inf_{n ≥ 1} c_n^{1/n}, the exact connective constant of ℤ³; reason: the decimal is the numerical value of the cubic lattice's connective constant, which is what the bound (58) is about
--   - encoding: P₃(H + V) a polynomial → C(H + V + 1)^k with C, k quantified before L, T, p, q and the decoder; reason: every polynomial is bounded by such an expression; the paper's P₃ does not depend on L, T, p, q
--   - encoding: Σ_V Σ_{H≥L} → V from 0 to L²T and H from L to 2L²T; reason: the link counts of p. 20; the remaining terms come from n_SAP(H, V) = 0
--   - encoding: (4μ₃²p̃), (4μ₃²q̃)^{·/2} powers → (√x)^n for x^{n/2}; reason: the same real number for x ≥ 0; avoids ℕ division in the exponent
--   - reading: a spacetime lattice of L×L sites over T time slices, with L²T sites, 2L²T horizontal and L²T vertical links (Sec. V B–C, pp. 19–20) → the 3-torus ZMod L × ZMod L × ZMod T with periodic time; links are (site, direction) pairs; reason: the counts printed on p. 20 are exactly those of the 3-torus; an open-time slab has L²(T−1) vertical links
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V C, eq. (59), p. 20

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_IsMLDecoder
import Definitions.Def_ToricMemory_Failure
import Definitions.Def_ToricMemory_CubicSAW

open Finset

namespace ToricMemory

/-- **Eq. (59)**, arXiv:quant-ph/0110143v1, Sec. V C, p. 20 (PDF p. 20):
`Prob_fail ≤ L²T Σ_V Σ_{H≥L} P₃(H + V) · (4μ₃² p̃)^{H/2}(4μ₃² q̃)^{V/2}`. There are `C` and `k`,
independent of `L, T, p, q` and the decoder, such that for all `L, T ≥ 1`, all `p, q ∈ [0, 1]`
and every maximum-likelihood decoder `D`,
`Prob_fail ≤ L²T Σ_{V=0}^{L²T} Σ_{H=L}^{2L²T} C(H + V + 1)^k (√(4μ₃²p̃))^H (√(4μ₃²q̃))^V`.

**Formalization Note** `P₃(H + V)` is encoded as `C (H + V + 1)^k`; the ranges of `H, V` are cut
at the link counts `2L²T`, `L²T`; `x^{H/2}` is written `(√x)^H`. -/
theorem eq_59 : ∃ C : ℝ, ∃ k : ℕ, ∀ (L T : ℕ) [NeZero L] [NeZero T] (p q : ℝ),
    0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
    ∀ D : Finset (Site L T) → Finset (Link L T), IsMLDecoder p q D →
      probFail p q D ≤
        (L : ℝ) ^ 2 * T * ∑ V ∈ range (L ^ 2 * T + 1), ∑ H ∈ Icc L (2 * L ^ 2 * T),
          C * ((H + V : ℕ) + 1 : ℝ) ^ k * Real.sqrt (4 * mu3 ^ 2 * (p * (1 - p))) ^ H *
            Real.sqrt (4 * mu3 ^ 2 * (q * (1 - q))) ^ V := by sorry

end ToricMemory
