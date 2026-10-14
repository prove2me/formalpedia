-- Prove2me | Theorems.Thm_RetailerMarketplace_Entry_lemma_1
-- name    : RetailerMarketplace.Entry.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:28.854981+00:00
-- url     : https://prove2.me/theorems/16f5147e-abde-4fe8-bb9c-b9c2815a75a2
-- title:
--   Lemma 1 with (1) and Property 1, pp. 5–6 — T enters exactly the products v ≥ v_T = c/(1 − f)
-- statement:
--   Let $c>0$, $f\in[0,1)$, $\lambda\in[0,1]$ and $v\in\mathbb R$, and let $v_T=c/(1-f)$ as in (1). Then
--   1. $T$'s monopoly profit is nonnegative exactly above the threshold: $\pi_T^{SBT}(v)=(1-f)v-c\ge 0\iff v\ge v_T$;
--   2. if $0<\lambda<1$, the same holds for her duopoly profit: $\pi_T^{SBMT}(v)\ge 0\iff v\ge v_T$;
--   3. at $v=v_T$ her duopoly price equals the threshold: $\bar p_T(v_T)=v_T$;
--   4. the products $T$ enters, those with $v(1-f)\ge c$, are exactly those with $v\ge v_T$:
--   $$v(1-f)\ge c\iff v\ge v_T=\frac{c}{1-f}.$$
--
--   This is Lemma 1 together with Property 1 (no entry deterrence): $T$'s entry decision does not depend on whether $M$ enters.
--
--   **Formalization Note** The duopoly clause is stated for $0<\lambda<1$: at $\lambda=1$ (and at $\lambda=0$) $\pi_T^{SBMT}\equiv 0$, so "$\pi_T^{SBMT}\ge 0$ iff $v\ge v_T$" fails below $v_T$. Entry at zero profit (at $v=v_T$) follows the paper's convention $v\ge v_T$. Assumption 1 is not needed and not assumed.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 6 (PDF p. 8), display (1) and Lemma 1; p. 5 (PDF p. 7), Property 1

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model

namespace RetailerMarketplace.Entry

/-- Lemma 1 with (1) and Property 1: T's monopoly profit is nonnegative exactly on `v ≥ v_T`; for
`0 < λ < 1` so is her duopoly profit; at `v = v_T` T's duopoly price equals `v_T`; and the products
T enters, `v(1 - f) ≥ c`, are exactly those with `v ≥ v_T = c/(1 - f)`. -/
theorem lemma_1 (c f lam v : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    (0 ≤ piSBT_T c f v ↔ vT c f ≤ v) ∧
      (0 < lam → lam < 1 → (0 ≤ piSBMT_T c f lam v ↔ vT c f ≤ v)) ∧
      pbarT c f lam (vT c f) = vT c f ∧
      (v ∈ mp c f ↔ vT c f ≤ v) := by sorry

end RetailerMarketplace.Entry
