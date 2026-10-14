-- Prove2me | Theorems.Thm_RetailerMarketplace_UnitFee_lemma_B_1_sbt_step
-- name    : RetailerMarketplace.UnitFee.lemma_B_1_sbt_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:10.071139+00:00
-- url     : https://prove2.me/theorems/9da0da29-00cf-4e0a-851a-1de399d31c2f
-- title:
--   Proof of Lemma B.1, p. 18 — SBT step: vf′ + t′ > vf* + t* iff v > v_T(f*, t*)
-- statement:
--   Let $c>0$, $f^*\in[0,1)$, $0<\varepsilon<t^*$, and let $(f',t')$ be the fees of the construction, $t'=t^*-\varepsilon$ and $f'=\frac{\varepsilon+f^*(c+t^*-\varepsilon)}{c+t^*}$. Then for every product valuation $v$, the monopolist's fee revenue in an SBT product market (where the third-party seller sells one unit at price $v$) is higher under $(f',t')$ exactly above the entry threshold:
--   $$vf'+t'>vf^*+t^* \iff v>v_T(f^*,t^*)=\frac{c+t^*}{1-f^*}.$$
--
--   This is the SBT step of the proof of Lemma B.1: on every product market served by the third-party seller alone, the switch of fees raises the monopolist's revenue.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 18 (PDF p. 20), Proof of Lemma B.1, second paragraph (SBT product markets)

import Mathlib
import Definitions.Def_RetailerMarketplace_UnitFee_Model

namespace RetailerMarketplace.UnitFee

/-- Proof of Lemma B.1, p. 18 (SBT step): with the fees `(f', t')` of the construction, M's fee
revenue in an SBT product market rises, `v f' + t' > v f* + t*`, exactly when `v > v_T(f*, t*)`. -/
theorem lemma_B_1_sbt_step (c fs ts ε f' t' : ℝ) (hc : 0 < c)
    (hfs : fs ∈ Set.Ico (0 : ℝ) 1) (hε : 0 < ε) (hεts : ε < ts)
    (hf' : f' = (ε + fs * (c + ts - ε)) / (c + ts)) (ht' : t' = ts - ε) (v : ℝ) :
    v * f' + t' > v * fs + ts ↔ vT c fs ts < v := by sorry

end RetailerMarketplace.UnitFee
