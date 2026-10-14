-- Prove2me | Theorems.Thm_RetailerMarketplace_UnitFee_lemma_B_1_construction
-- name    : RetailerMarketplace.UnitFee.lemma_B_1_construction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:57.044343+00:00
-- url     : https://prove2.me/theorems/655756aa-3552-4493-b55e-7d321e3efa8d
-- title:
--   Proof of Lemma B.1, p. 18 — t′ = t* − ε, f′ = (ε + f*(c + t* − ε))/(c + t*) keep v_T unchanged
-- statement:
--   Let $c>0$, let $f^*\in[0,1)$ and $t^*>0$ be fees, and let $0<\varepsilon<t^*$. Define the alternative fees
--   $$t'=t^*-\varepsilon,\qquad f'=\frac{\varepsilon+f^*(c+t^*-\varepsilon)}{c+t^*}.$$
--   Then $t'>0$, $f^*<f'<1$, and the entry threshold is unchanged:
--   $$v_T(f',t')=\frac{c+t'}{1-f'}=\frac{c+t^*}{1-f^*}=v_T(f^*,t^*),$$
--   so the set of products the third-party sellers enter is the same under both fee pairs.
--
--   This is the construction at the heart of the proof of Lemma B.1: a part of the per-unit fee is converted into a higher ad valorem fee, leaving every seller's entry decision as it was.
--
--   **Formalization Note.** The hypotheses $\varepsilon<t^*$ (equivalently $t'>0$) and $f^*<1$ are those of the proof; $f'<1$ holds exactly when $f^*<1$. The last conclusion is stated as equality of the marketplace sets $\{v : v(1-f)\ge c+t\}$.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 18 (PDF p. 20), Proof of Lemma B.1, first paragraph

import Mathlib
import Definitions.Def_RetailerMarketplace_UnitFee_Model

namespace RetailerMarketplace.UnitFee

/-- Proof of Lemma B.1, p. 18: for `t* > 0` and `0 < ε < t*`, the fees `t' = t* - ε` and
`f' = (ε + f* (c + t* - ε)) / (c + t*)` satisfy `t' > 0`, `f* < f' < 1`, and leave the entry
threshold `v_T` and the set of marketplace products unchanged. -/
theorem lemma_B_1_construction (c fs ts ε f' t' : ℝ) (hc : 0 < c)
    (hfs : fs ∈ Set.Ico (0 : ℝ) 1) (hε : 0 < ε) (hεts : ε < ts)
    (hf' : f' = (ε + fs * (c + ts - ε)) / (c + ts)) (ht' : t' = ts - ε) :
    0 < t' ∧ fs < f' ∧ f' < 1 ∧ vT c f' t' = vT c fs ts ∧ mp c f' t' = mp c fs ts := by sorry

end RetailerMarketplace.UnitFee
