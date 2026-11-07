-- Prove2me | Theorems.Thm_StretchDepth_dagger
-- name    : StretchDepth.dagger
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:43.447181+00:00
-- url     : https://prove2.me/theorems/efc12a35-89f6-4526-b9c1-688639649a4d
-- title:
--   Proof of Lemma 1 — the bound (†)
-- statement:
--   In the setting of the Critical Query bound, for every input $x$,
--   $$
--   \mathbb E_\rho\sum_{t=0}^q|Y^\rho_{x,t}|\le(q+1)\bigl(d(q+1)^2+1\bigr)\,2^{M-M\left(\frac{n-\log_2 qs}{N}\right)^d}.
--   $$
--   Summing over $x$ yields Lemma 1 at once.
--
--   Differences from the source:
--   - generalization: poly(qd) → the explicit (q+1)(d(q+1)^2+1); reason: the value the proof yields, at most 10(qd)^3 for q, d >= 1
--   - reading: Definition 1: without loss of generality no input is queried more than once → hypothesis NoRepeat H; reason: the proof on p.17 invokes it; no_repeat_normal_form removes it for Lemma 1, and the bound fails without it (q = 2, d = 1, n = 3, s = 1, a repeated query: Pr[t = 2] = 1/8 > 1/16)
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Lemma 1, p.16

import Definitions.Def_StretchDepth_IsConstruction
import Definitions.Def_StretchDepth_crit

namespace StretchDepth

/-- **The bound (†).**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Lemma 1, p.16: "We will show that for all x ∈ {0, 1}m we have:
Eρ Σ_{t=0}^q |Y ρ x,t| ≤ poly(qd) · 2^{M−M((n−log qs)/N)^d} (†)".

**Formalization Note.** `poly(qd)` is the value `(q+1)(d(q+1)²+1)` that the proof yields: the bad
event contributes `(q+1) 2^M d(q+1)² 2^{−τα}` and the rest `(q+1) 2^{(N−ℓ)τ}`, at the `τ` with
`M − τα = (N−ℓ)τ`. `NoRepeat H` is as in `critical_query_bound`. -/
theorem dagger {n N m M : ℕ} (hN : n < N) (q d : ℕ) (hq : 1 ≤ q) (hd : 1 ≤ d) (s : ℝ)
    (hs : 1 ≤ s) (hqs : (q : ℝ) * s < 2 ^ n) (H : Bits m → RoundTree n N M)
    (hH : IsConstruction H q d) (hNR : NoRepeat H) (x : Bits m) :
    expRho (s / 2 ^ n) (fun ρ : PartialAssign n N =>
        ∑ k ∈ Finset.range (q + 1), ((Y ρ (H x) k).card : ℝ)) ≤
      ((q : ℝ) + 1) * ((d : ℝ) * ((q : ℝ) + 1) ^ 2 + 1) *
        (2 : ℝ) ^ ((M : ℝ) - M * (ell n q s / N) ^ d) := by sorry

end StretchDepth
