-- Prove2me | Theorems.Thm_StrategicQR_Game_lemma5_qr_sale_price
-- name    : StrategicQR.Game.lemma5_qr_sale_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:49.138984+00:00
-- url     : https://prove2.me/theorems/87a54ea8-4533-46f3-a83b-342c03f053e6
-- title:
--   Lemma 5 (i), p. 19 — the optimal sale price with quick response: $s_l, s_m, s_h(D), s_r$
-- statement:
--   Let $0<\alpha\le1$, $q>0$, $\hat v\in[\underline v,\bar v)$, $v_B<c_2\le p$ and $D\ge0$, and let $I=(q-\xi D)^+$. The retailer with quick response chooses a sale price $s\in[0,p]$ and a sale-period replenishment $q_2\ge0$ to maximize $R(s,I,q_2)$. Let
--   $$s^*=\begin{cases}s_r & D_r<D,\\ s_h(D) & D_m<D\le D_r,\\ s_m & D_l<D\le D_m,\\ s_l & D\le D_l.\end{cases}$$
--
--   1. If $c_2\le\bar v$ and $\xi+\bar G(s_r)\alpha>0$, then $s^*\in[0,p]$ and, for a suitable $q_2\ge0$, the pair $(s^*,q_2)$ maximizes $R(s,I,q_2)$. If moreover $c_2<\bar v$ and $D\ne D_l$, every maximizing pair has price $s^*$.
--   2. If $c_2>\bar v$, every maximizing pair has $q_2=0$: reactive capacity is never used for the sale period. For $D\le D_h$, the price of Lemma 2 together with $q_2=0$ is a maximizing pair, and for $D<D_h$ with $D\ne D_l$ every maximizing pair has the price of Lemma 2: the optimal sale price is identical to that of Lemma 2.
--
--   The retailer never prices above $s_r$, the optimal price when the marginal unit is bought at $c_2$, and the deep discount $s_l$ is offered exactly as without quick response.
--
--   **Formalization Note**
--   - **Uniqueness.** As in Lemma 2, the printed "unique" fails at $D=D_l$ ($s_l$ and $s_m$ tie). It also fails at $c_2=\bar v$ and $D>D_h$, where every price $s\ge\bar v$ earns $0$. Uniqueness is stated where it holds.
--   - **Finite $D_r$.** $\xi+\bar G(s_r)\alpha>0$ excludes the corner $\xi=0$, $c_2=\bar v$, where $D_r=+\infty$.
--   - **Typo.** The page's "$D_r\le D_h$ from Theorem 1" refers to Lemma 2.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 19, Lemma 5 (i); Technical Appendix pp. 4–6 (PDF 36–38), proof of Lemma 5

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Lemma 5 (i) (p. 19; proof on Technical Appendix pp. 4–6), the optimal sale price with quick
response, with the uniqueness claim corrected. Let `0 < α ≤ 1`, `q > 0`, `v̂ ∈ [v̲, v̄)`,
`vB < c₂ ≤ p` and `D ≥ 0`, and let `I = (q - ξD)⁺`.
1. If `c₂ ≤ v̄` and `D_r` is finite (`ξ + Ḡ(s_r) α > 0`), the price `s*` (`s_l`, `s_m`, `s_h(D)` or `s_r`) is admissible and, with a
   suitable `q₂ ≥ 0`, maximizes `R(s, I, q₂)` over `s ∈ [0, p]`, `q₂ ≥ 0`; if `c₂ < v̄` and
   `D ≠ D_l`, every maximizing pair has price `s*`.
2. If `c₂ > v̄`, every maximizing pair has `q₂ = 0` (reactive capacity is never used for the
   sale period), for `D ≤ D_h` the Lemma 2 price with `q₂ = 0` is a maximizing pair, and for
   `D < D_h`, `D ≠ D_l` every maximizing pair has the Lemma 2 price (the optimal sale price is
   identical to that of Lemma 2). -/
theorem lemma5_qr_sale_price (M : Model) {α q vhat c₂ D : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hq : 0 < q) (hv : vhat ∈ Set.Ico M.vlo M.vhi) (hc₂ : M.vB < c₂) (hc₂p : c₂ ≤ M.p)
    (hD : 0 ≤ D) :
    (c₂ ≤ M.vhi → 0 < xi M α vhat + Gbar M (sr M c₂ vhat) * α →
      qrSalePriceStar M α c₂ q vhat D ∈ Set.Icc 0 M.p ∧
      (∃ q₂ ∈ Set.Ici (0 : ℝ),
        IsMaxOn (fun z : ℝ × ℝ => qrSaleRevenue M α c₂ D vhat z.1 (max (q - xi M α vhat * D) 0) z.2)
          (Set.Icc 0 M.p ×ˢ Set.Ici 0) (qrSalePriceStar M α c₂ q vhat D, q₂)) ∧
      (c₂ < M.vhi → D ≠ Dl M α q vhat → ∀ z ∈ Set.Icc 0 M.p ×ˢ Set.Ici (0 : ℝ),
        IsMaxOn (fun z : ℝ × ℝ => qrSaleRevenue M α c₂ D vhat z.1 (max (q - xi M α vhat * D) 0) z.2)
          (Set.Icc 0 M.p ×ˢ Set.Ici 0) z → z.1 = qrSalePriceStar M α c₂ q vhat D)) ∧
    (M.vhi < c₂ →
      (∀ z ∈ Set.Icc 0 M.p ×ˢ Set.Ici (0 : ℝ),
        IsMaxOn (fun z : ℝ × ℝ => qrSaleRevenue M α c₂ D vhat z.1 (max (q - xi M α vhat * D) 0) z.2)
          (Set.Icc 0 M.p ×ˢ Set.Ici 0) z → z.2 = 0) ∧
      (xi M α vhat * D ≤ q →
        IsMaxOn (fun z : ℝ × ℝ => qrSaleRevenue M α c₂ D vhat z.1 (max (q - xi M α vhat * D) 0) z.2)
          (Set.Icc 0 M.p ×ˢ Set.Ici 0) (salePriceStar M α q vhat D, 0)) ∧
      (xi M α vhat * D < q → D ≠ Dl M α q vhat → ∀ z ∈ Set.Icc 0 M.p ×ˢ Set.Ici (0 : ℝ),
        IsMaxOn (fun z : ℝ × ℝ => qrSaleRevenue M α c₂ D vhat z.1 (max (q - xi M α vhat * D) 0) z.2)
          (Set.Icc 0 M.p ×ˢ Set.Ici 0) z → z.1 = salePriceStar M α q vhat D)) := by sorry

end StrategicQR.Game
