-- Prove2me | Theorems.Thm_ProxGapTight_amp_coordinate_prob
-- name    : ProxGapTight.amp_coordinate_prob
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:49:30.348465+00:00
-- url     : https://prove2.me/theorems/6d056c57-f155-4d9e-9ebb-0b17d6dde0b9
-- title:
--   Proof of Theorem 3.1, p.13 — $\Pr[A(v)_j\neq0]=(1-1/q)\Phi_t(u)$
-- statement:
--   Let $\mathbb F_q$ be a finite field, $E$ a finite $\mathbb F_q$-vector space, $n,t\ge1$, and $v\in E^n$ of relative weight $u=\mathrm{wt}(v)/n$. Sample $i_1,\dots,i_t\in[n]$ uniformly with replacement and a uniformly random $\mathbb F_q$-linear functional $\ell:E^t\to\mathbb F_q$, independently. Then
--   $$
--   \Pr\big[\ell(v_{i_1},\dots,v_{i_t})\neq0\big]=\Big(1-\frac1q\Big)\Phi_t(u).
--   $$
--
--   This is the expected relative weight of the amplified word $A(v)$, one coordinate at a time.
--
--   **Formalization Note** The probability is the fraction of choices (index tuple, functional) satisfying the event, which is exact for these finite uniform laws.
--
--   Differences from the source:
--   - generalization: v ∈ (F_{q^r})^{n_m} and ℓ_j : (F_{q^r})^t → F_q → v ∈ E^n and ℓ : E^t → F for any finite F-module E; reason: the paper's case is E = F_{q^r} viewed over F_q
--   - generalization: F_q → any finite field F, q = Fintype.card F; reason: the statement specializes to F_q
--   - encoding: Pr over uniform independent choices → cardinality ratio over AmpSample F E n t; reason: exact for finite uniform laws
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), proof of Theorem 3.1, p.13, display

import Mathlib
import Definitions.Def_ProxGapTight_Phi
import Definitions.Def_ProxGapTight_amp

namespace ProxGapTight

/-- **One coordinate of the amplification**, proof of Theorem 3.1, Kominers, Thaler, Zheng,
manuscript (Sept. 2026), p.13, display: "If v has relative weight u, then
Pr[A(v)_j ≠ 0] = (1 − 1/q) Φ_t(u)."

**Formalization Note.** `F_q` is any finite field `F` (`q = |F|`) and the paper's `F_{q^r}` any
finite `F`-module `E`. One coordinate's randomness is the uniform law on
`AmpSample F E n t = (Fin t → Fin n) × ((Fin t → E) →ₗ[F] F)` (indices with replacement, a uniform
functional), so the probability is a cardinality ratio. `u = wt(v)/n`. -/
theorem amp_coordinate_prob (F E : Type) [Field F] [Fintype F] [AddCommGroup E] [Module F E]
    [Fintype E] [DecidableEq E] (n t : ℕ) (hn : 0 < n) (ht : 1 ≤ t) (v : Fin n → E) :
    (Nat.card {ω : AmpSample F E n t // ω.2 (fun k => v (ω.1 k)) ≠ 0} : ℝ) /
        (Nat.card (AmpSample F E n t) : ℝ) =
      (1 - 1 / (Fintype.card F : ℝ)) * Phi t ((hammingNorm v : ℝ) / (n : ℝ)) := by sorry

end ProxGapTight
