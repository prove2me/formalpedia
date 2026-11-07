-- Prove2me | Theorems.Thm_StretchDepth_key_claim_2
-- name    : StretchDepth.key_claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:54.324401+00:00
-- url     : https://prove2.me/theorems/7a525385-2177-4691-abaf-e5d6294a28ab
-- title:
--   Proof of Lemma 1 — key claim 2
-- statement:
--   In the setting of the Critical Query bound, for all $0\le t\le q$,
--   $$
--   \mathbb E_\rho\,|Y^\rho_{x,t}|\le2^{(N-\ell)t}.
--   $$
--   Together with key claim 1 this bounds the expected size of the set of reachable outputs, by choosing the threshold that balances the two.
--
--   Differences from the source:
--   - reading: Definition 1: without loss of generality no input is queried more than once → hypothesis NoRepeat H; reason: the proof on p.17 invokes it; no_repeat_normal_form removes it for Lemma 1, and the bound fails without it (q = 2, d = 1, n = 3, s = 1, a repeated query: Pr[t = 2] = 1/8 > 1/16)
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Lemma 1, p.16

import Definitions.Def_StretchDepth_IsConstruction
import Definitions.Def_StretchDepth_crit

namespace StretchDepth

/-- **Key claim 2 of Lemma 1.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Lemma 1, p.16: "Eρ|Y ρ x,t| ≤ 2(N−ℓ)t for all 0 ≤ t ≤ q."

**Formalization Note.** `NoRepeat H` is as in `critical_query_bound`: the proof on p.17 says "As
before", and the bound fails with repeated queries. -/
theorem key_claim_2 {n N m M : ℕ} (hN : n < N) (q d : ℕ) (hq : 1 ≤ q) (hd : 1 ≤ d) (s : ℝ)
    (hs : 1 ≤ s) (hqs : (q : ℝ) * s < 2 ^ n) (H : Bits m → RoundTree n N M)
    (hH : IsConstruction H q d) (hNR : NoRepeat H) (x : Bits m) (k : ℕ) (hk : k ≤ q) :
    expRho (s / 2 ^ n) (fun ρ : PartialAssign n N => ((Y ρ (H x) k).card : ℝ)) ≤
      (2 : ℝ) ^ (((N : ℝ) - ell n q s) * k) := by sorry

end StretchDepth
