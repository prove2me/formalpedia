-- Prove2me | Theorems.Thm_StretchDepth_key_claim_1
-- name    : StretchDepth.key_claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:41.645741+00:00
-- url     : https://prove2.me/theorems/248533dc-b878-4464-b39a-e057e4892578
-- title:
--   Proof of Lemma 1 — key claim 1
-- statement:
--   In the setting of the Critical Query bound, for every threshold $\tau\ge0$,
--   $$
--   \Pr_\rho\bigl[\exists t\ge\tau,\ Y^\rho_{x,t}\ne\emptyset\bigr]\le d(q+1)^2\,2^{-\tau\alpha},
--   $$
--   where $\alpha=(N-\ell)/((N/\ell)^d-1)$. The factor $d(q+1)^2$ does not depend on $\tau$.
--
--   So executions with many critical queries are unlikely, at a rate set by the depth $d$.
--
--   Differences from the source:
--   - generalization: poly(qd) → the explicit d(q+1)^2; reason: the value at the end of the display on p.17; it is a polynomial in qd for q, d >= 1
--   - reading: Definition 1: without loss of generality no input is queried more than once → hypothesis NoRepeat H; reason: the proof on p.17 invokes it; no_repeat_normal_form removes it for Lemma 1, and the bound fails without it (q = 2, d = 1, n = 3, s = 1, a repeated query: Pr[t = 2] = 1/8 > 1/16)
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Lemma 1, p.16

import Definitions.Def_StretchDepth_IsConstruction
import Definitions.Def_StretchDepth_crit

namespace StretchDepth

/-- **Key claim 1 of Lemma 1.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Lemma 1, p.16: "For any threshold τ ≥ 0, Prρ[∃t ≥ τ, Y ρ x,t ≠ ∅] ≤ poly(qd) · 2−τα
(where the poly(qd) term does not depend on the threshold τ)."

**Formalization Note.** `poly(qd)` is the value `d(q+1)²` at the end of the display on p.17.
`NoRepeat H` is as in `critical_query_bound`. -/
theorem key_claim_1 {n N m M : ℕ} (hN : n < N) (q d : ℕ) (hq : 1 ≤ q) (hd : 1 ≤ d) (s : ℝ)
    (hs : 1 ≤ s) (hqs : (q : ℝ) * s < 2 ^ n) (H : Bits m → RoundTree n N M)
    (hH : IsConstruction H q d) (hNR : NoRepeat H) (x : Bits m) (τ : ℝ) (hτ : 0 ≤ τ) :
    probRho (s / 2 ^ n) (fun ρ : PartialAssign n N =>
        ∃ k : ℕ, τ ≤ k ∧ (Y ρ (H x) k).Nonempty) ≤
      (d : ℝ) * ((q : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (-(τ * alpha N (ell n q s) d)) := by sorry

end StretchDepth
