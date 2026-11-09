-- Prove2me | Theorems.Thm_ProxGapTight_amp_chernoff
-- name    : ProxGapTight.amp_chernoff
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:51:11.455985+00:00
-- url     : https://prove2.me/theorems/727e26d2-3cce-4898-8a19-5735e10e100f
-- title:
--   Proof of Theorem 3.1, p.13 — Chernoff bound $2e^{-2\xi^2N}$ for a fixed word
-- statement:
--   Let $\mathbb F_q$ be a finite field, $E$ a finite $\mathbb F_q$-vector space, $n,t,N\ge1$, $\xi>0$ and $v\in E^n$ of relative weight $u=\mathrm{wt}(v)/n$. Let $A$ be the amplification map with all indices and functionals chosen uniformly and independently. Then
--   $$
--   \Pr\Big[\Big|\frac{\mathrm{wt}(A(v))}{N}-\Big(1-\frac1q\Big)\Phi_t(u)\Big|>\xi\Big]\le 2e^{-2\xi^2N}.
--   $$
--
--   In the proof this bound is combined with a union bound over all of $D_m=\mathrm{span}_{\mathbb F_{q^r}}(U_m)$, so that a single map $A$ amplifies every relevant distance at once.
--
--   **Formalization Note** The probability is a fraction of the finitely many choices of the map.
--
--   Differences from the source:
--   - generalization: fixed v ∈ D_m = span_{F_{q^r}}(U_m) → every v ∈ E^n; reason: the bound uses only that v is fixed
--   - generalization: F_{q^r} over F_q → any finite F-module E over any finite field F; reason: the paper's case is E = F_{q^r}, F = F_q
--   - encoding: the Chernoff bound 'relative weight within ξ of (1 − 1/q)Φ_t(u)' fails → ξ < |wt(A(v))/N − (1 − 1/q)Φ_t(wt(v)/n)|, probability as a cardinality ratio; reason: complement of 'within ξ'; exact for finite uniform laws
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), proof of Theorem 3.1, p.13 ('Hence, by a Chernoff bound …'; 'For any fixed v ∈ D_m, the preceding Chernoff bound fails with probability at most 2e^{−2ξ²N}')

import Mathlib
import Definitions.Def_ProxGapTight_Phi
import Definitions.Def_ProxGapTight_amp

namespace ProxGapTight

/-- **Chernoff bound for a fixed word**, proof of Theorem 3.1, Kominers, Thaler, Zheng, manuscript
(Sept. 2026), p.13: "the relative weight of A(v) is within ξ of this quantity except with
probability e^{−Ω_ξ(N)}" and "For any fixed v ∈ D_m, the preceding Chernoff bound fails with
probability at most 2e^{−2ξ²N}."

**Formalization Note.** The amplification map's randomness is the uniform law on
`Fin N → AmpSample F E n t` (independent coordinates); "fails" is `|wt(A(v))/N − (1 − 1/q)Φ_t(u)| > ξ`
with `u = wt(v)/n`. Stated for every `v`, not only `v ∈ D_m`. -/
theorem amp_chernoff (F E : Type) [Field F] [Fintype F] [DecidableEq F] [AddCommGroup E]
    [Module F E] [Fintype E] [DecidableEq E] (n t N : ℕ) (hn : 0 < n) (ht : 1 ≤ t) (hN : 1 ≤ N)
    (ξ : ℝ) (hξ : 0 < ξ) (v : Fin n → E) :
    (Nat.card {ω : Fin N → AmpSample F E n t //
        ξ < |(hammingNorm (amp ω v) : ℝ) / (N : ℝ) -
          (1 - 1 / (Fintype.card F : ℝ)) * Phi t ((hammingNorm v : ℝ) / (n : ℝ))|} : ℝ) /
        (Nat.card (Fin N → AmpSample F E n t) : ℝ) ≤
      2 * Real.exp (-2 * ξ ^ 2 * (N : ℝ)) := by sorry

end ProxGapTight
