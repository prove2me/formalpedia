-- Prove2me | Theorems.Thm_StrategicQR_Game_lemma5_qr_quasiconcave
-- name    : StrategicQR.Game.lemma5_qr_quasiconcave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:34.797399+00:00
-- url     : https://prove2.me/theorems/0bbcc15f-8fc6-46bc-bf11-bc3d5550103f
-- title:
--   Lemma 5 (ii), p. 19 — $\pi_r(q,\hat v)$ is quasi-concave in $q$, with derivative (4)
-- statement:
--   Assume MSLR, $0<\alpha\le1$, $v_B<c_1\le c_2\le p$, and fix a belief $\hat v\in[\underline v,\bar v]$. Then:
--
--   1. the profit with quick response $q\mapsto\pi_r(q,\hat v)$ is quasi-concave on $[0,\infty)$;
--   2. if $c_2\le\bar v$ and $\xi+\bar G(s_r)\alpha>0$ (so that $D_r$ is finite), then for every $q>0$
--   $$\frac{d\pi_r(q,\hat v)}{dq}=c_2-c_1-c_2F(D_r)+s_lF(D_l)+\int_{D_m}^{D_r}(2s_h(x)-\bar v)\,dF(x).\qquad(4)$$
--
--   Quasi-concavity gives existence of an equilibrium with quick response exactly as in Theorem 1; the derivative (4) drives the analysis of when all strategic consumers buy early.
--
--   **Formalization Note** The appendix prints $F(D_h^r)$ in (4); the re-derived term, confirmed numerically, is $F(D_r)$. The appendix proof refers to "the same manner as Theorem 2", which should read Lemma 3. The derivative formula is the one the appendix states, for $c_2\le\bar v$.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 19, Lemma 5 (ii); Technical Appendix pp. 5–6 (PDF 37–38), proof of Lemma 5, eq. (4)

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Lemma 5 (ii) (p. 19; proof on Technical Appendix pp. 5–6). Under MSLR, for `0 < α ≤ 1`,
`vB < c₁ ≤ c₂ ≤ p` and any belief `v̂ ∈ [v̲, v̄]`, the profit with quick response
`q ↦ π_r(q, v̂)` is quasi-concave on `[0, ∞)`; and when `c₂ ≤ v̄` and `D_r` is finite
(`ξ + Ḡ(s_r) α > 0`), its derivative at every `q > 0` is the right side of (4),
`c₂ - c₁ - c₂ F(D_r) + s_l F(D_l) + ∫_{D_m}^{D_r} (2 s_h(x) - v̄) dF(x)`. -/
theorem lemma5_qr_quasiconcave (M : Model) (hmslr : MSLR M.f) {α c₁ c₂ vhat : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hc₁ : M.vB < c₁) (hc₁₂ : c₁ ≤ c₂) (hc₂p : c₂ ≤ M.p)
    (hv : vhat ∈ Set.Icc M.vlo M.vhi) :
    QuasiconcaveOn ℝ (Set.Ici 0) (fun q => qrProfit M α c₁ c₂ q vhat) ∧
    (c₂ ≤ M.vhi → 0 < xi M α vhat + Gbar M (sr M c₂ vhat) * α →
      ∀ q, 0 < q → HasDerivAt (fun q' => qrProfit M α c₁ c₂ q' vhat)
        (focQRProfit M α c₁ c₂ q vhat) q) := by sorry

end StrategicQR.Game
