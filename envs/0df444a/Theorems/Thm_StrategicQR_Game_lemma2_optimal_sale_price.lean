-- Prove2me | Theorems.Thm_StrategicQR_Game_lemma2_optimal_sale_price
-- name    : StrategicQR.Game.lemma2_optimal_sale_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:24:43.53649+00:00
-- url     : https://prove2.me/theorems/21d87cf5-46fc-433e-879d-620ad1742776
-- title:
--   Lemma 2, p. 12 — the optimal sale price $s^*(D)\in\{s_l, s_m, s_h(D)\}$ with critical levels $D_l, D_m, D_h$
-- statement:
--   Let $0<\alpha\le1$, $q>0$ and $\hat v\in[\underline v,\bar v)$, and let $D\ge0$ be a demand level with $\xi D\le q$, i.e. $D\le D_h$ (when $\xi=0$, every $D$). Let $I=(q-\xi D)^+$ be the inventory at the start of the sale period, and let
--   $$s^*(D)=\begin{cases}s_h(D) & D_m<D\le D_h,\\ s_m & D_l<D\le D_m,\\ s_l & D\le D_l,\end{cases}$$
--   with $s_l=v_B$, $s_m=\max(\bar v/2,\hat v)$, $s_h(D)=(\bar v-\underline v)(D-q)/(\alpha D)+\hat v$ and $D_l, D_m, D_h$ as in the critical-levels module. Then
--
--   1. $s^*(D)\in[0,p]$, and $s^*(D)$ maximizes the sale revenue $R(s,I)$ over all prices $s\in[0,p]$;
--   2. if moreover $\xi D<q$ and $D\ne D_l$, then $s^*(D)$ is the only maximizer.
--
--   The form of the optimal markdown is natural: deep discount $s_l$ to clear ample inventory, the revenue-maximizing price $s_m$ for the strategic segment with moderately ample inventory, and the clearing price $s_h(D)$ when inventory is scarce.
--
--   **Formalization Note** The page claims a unique optimal price for every $D$. That fails in two places, so uniqueness is stated where it holds:
--   - at $D=D_l$, $s_l$ and $s_m$ earn the same revenue (that is how $D_l$ is defined, Technical Appendix p. 2);
--   - at $D=D_h$, $I=0$ and every price earns $0$.
--
--   The hypotheses $q>0$, $\alpha>0$ and $\hat v<\bar v$ are implicit on the page: $s_h$ divides by $\alpha D$, and $s_m$, $D_m$ need a nonempty strategic segment that waits.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 12, Lemma 2; Technical Appendix pp. 1–2 (PDF 33–34), proof of Lemma 2

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Lemma 2 (p. 12; proof on Technical Appendix pp. 1–2), the optimal sale price, with the
uniqueness claim corrected. For a nonempty strategic segment (`0 < α ≤ 1`), an order `q > 0`, a
belief `v̂ ∈ [v̲, v̄)` and a demand level `D ≥ 0` with `ξ D ≤ q` (i.e. `D ≤ D_h`, and every `D`
when `ξ = 0`), the price `s*(D)` (`s_l`, `s_m` or `s_h(D)`) is an admissible price that
maximizes the sale-period revenue `R(s, I)`, `I = (q - ξD)⁺`, over `s ∈ [0, p]`; and it is the
unique maximizer when `ξ D < q` and `D ≠ D_l`. -/
theorem lemma2_optimal_sale_price (M : Model) {α q vhat D : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hq : 0 < q) (hv : vhat ∈ Set.Ico M.vlo M.vhi) (hD : 0 ≤ D)
    (hDh : xi M α vhat * D ≤ q) :
    salePriceStar M α q vhat D ∈ Set.Icc 0 M.p ∧
    IsMaxOn (fun s => saleRevenue M α D vhat s (max (q - xi M α vhat * D) 0)) (Set.Icc 0 M.p)
      (salePriceStar M α q vhat D) ∧
    (xi M α vhat * D < q → D ≠ Dl M α q vhat → ∀ s ∈ Set.Icc 0 M.p,
      IsMaxOn (fun s' => saleRevenue M α D vhat s' (max (q - xi M α vhat * D) 0))
        (Set.Icc 0 M.p) s → s = salePriceStar M α q vhat D) := by sorry

end StrategicQR.Game
