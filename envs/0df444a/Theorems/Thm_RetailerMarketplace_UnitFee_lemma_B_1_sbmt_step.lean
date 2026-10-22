-- Prove2me | Theorems.Thm_RetailerMarketplace_UnitFee_lemma_B_1_sbmt_step
-- name    : RetailerMarketplace.UnitFee.lemma_B_1_sbmt_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:58.556985+00:00
-- url     : https://prove2.me/theorems/f255b645-86d9-4c6e-9c47-f4f033fa2038
-- title:
--   Proof of Lemma B.1, p. 18 — SBMT step: p̄_T(f′, t′)f′ + t′ > p̄_T(f*, t*)f* + t* iff v > v_T(f*, t*)
-- statement:
--   Let $c>0$, $f^*\in[0,1)$, $0<\varepsilon<t^*$, $\lambda\in[1/2,1]$, and let $(f',t')$ be the fees of the construction, $t'=t^*-\varepsilon$ and $f'=\frac{\varepsilon+f^*(c+t^*-\varepsilon)}{c+t^*}$. Write $\bar p_T(f,t)=\frac{\lambda v+(1-\lambda)(c+t)}{1-f(1-\lambda)}$ for the third-party seller's SBMT price (B.1). Then for every product valuation $v$, the fee the monopolist collects per unit the third-party seller sells in an SBMT product market is higher under $(f',t')$ exactly above the entry threshold:
--   $$\bar p_T(f',t')\,f'+t'>\bar p_T(f^*,t^*)\,f^*+t^* \iff v>v_T(f^*,t^*)=\frac{c+t^*}{1-f^*}.$$
--
--   This is the SBMT step of the proof of Lemma B.1: on every product market where both firms sell, the switch of fees raises the monopolist's fee income (which is $1-\lambda$ times the per-unit amount above).
--
--   **Formalization Note.** $\lambda\ge1/2$ is the paper's standing Assumption 1.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 18 (PDF p. 20), Proof of Lemma B.1, second paragraph (SBMT product markets), with display (B.1)

import Mathlib
import Definitions.Def_RetailerMarketplace_UnitFee_Model

namespace RetailerMarketplace.UnitFee

/-- Proof of Lemma B.1, p. 18 (SBMT step): with the fees `(f', t')` of the construction, the fee
M collects per unit T sells in an SBMT product market rises,
`p̄_T(f', t') f' + t' > p̄_T(f*, t*) f* + t*` with `p̄_T` from (B.1), exactly when
`v > v_T(f*, t*)`. -/
theorem lemma_B_1_sbmt_step (c fs ts ε f' t' lam : ℝ) (hc : 0 < c)
    (hfs : fs ∈ Set.Ico (0 : ℝ) 1) (hε : 0 < ε) (hεts : ε < ts)
    (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hf' : f' = (ε + fs * (c + ts - ε)) / (c + ts)) (ht' : t' = ts - ε) (v : ℝ) :
    pbarT c f' t' lam v * f' + t' > pbarT c fs ts lam v * fs + ts ↔ vT c fs ts < v := by sorry

end RetailerMarketplace.UnitFee
