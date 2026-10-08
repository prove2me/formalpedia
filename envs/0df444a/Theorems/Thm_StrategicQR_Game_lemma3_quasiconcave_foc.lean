-- Prove2me | Theorems.Thm_StrategicQR_Game_lemma3_quasiconcave_foc
-- name    : StrategicQR.Game.lemma3_quasiconcave_foc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:18.268157+00:00
-- url     : https://prove2.me/theorems/c646f1ff-aade-4d7c-b364-776cbfa4e08b
-- title:
--   Lemma 3, p. 13 — $\pi(q,\hat v)$ is quasi-concave in $q$; the optimal order solves the first-order condition (2)
-- statement:
--   Assume the demand density has the MSLR property, $0<\alpha\le1$, $v_B<c<p$, and fix a belief $\hat v\in[\underline v,\bar v]$. Then:
--
--   1. the retailer's profit $q\mapsto\pi(q,\hat v)$ is quasi-concave on $[0,\infty)$;
--   2. if $\xi>0$, then for every $q>0$
--   $$\frac{d\pi(q,\hat v)}{dq}=p-c-pF(D_h)+s_lF(D_l)+\int_{D_m}^{D_h}(2s_h(x)-\bar v)\,dF(x);\qquad(2)$$
--   3. if $\xi>0$, the right side of (2) has exactly one zero $q_0>0$, and $q_0$ is the unique maximizer of $\pi(\cdot,\hat v)$ on $[0,\infty)$.
--
--   Unlike the newsvendor profit ($\alpha=0$), $\pi(\cdot,\hat v)$ is in general not concave; quasi-concavity is what makes the retailer's best response unique and is the key step towards the existence of an equilibrium.
--
--   **Formalization Note** The page's $D_h=q/\xi$ is $+\infty$ when $\xi=0$ (that is, $\alpha=1$ and $\hat v=\underline v$), and the formula (2) then needs $F(D_h)=1$. The derivative and first-order-condition claims are therefore stated for $\xi>0$. The bound $c<p$ is what the proof of Theorem 1 uses ($p-c>0$).
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 13, Lemma 3, eq. (2); Technical Appendix pp. 3–4 (PDF 35–36), proof of Lemma 3

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Lemma 3 (p. 13; proof on Technical Appendix pp. 3–4). Under MSLR, for `0 < α ≤ 1`,
`vB < c < p` and any belief `v̂ ∈ [v̲, v̄]`, the profit `q ↦ π(q, v̂)` is quasi-concave on
`[0, ∞)`; and when `ξ > 0` (so that `D_h = q/ξ` is finite) its derivative at every `q > 0` is the
right side of (2), `p - c - pF(D_h) + s_l F(D_l) + ∫_{D_m}^{D_h} (2 s_h(x) - v̄) dF(x)`, this
expression has exactly one zero `q₀ > 0`, and `q₀` is the unique maximizer of `π(·, v̂)` on
`[0, ∞)`. -/
theorem lemma3_quasiconcave_foc (M : Model) (hmslr : MSLR M.f) {α c vhat : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : M.vB < c) (hcp : c < M.p)
    (hv : vhat ∈ Set.Icc M.vlo M.vhi) :
    QuasiconcaveOn ℝ (Set.Ici 0) (fun q => profit M α c q vhat) ∧
    (0 < xi M α vhat →
      (∀ q, 0 < q → HasDerivAt (fun q' => profit M α c q' vhat) (focProfit M α c q vhat) q) ∧
      (∃! q₀, 0 < q₀ ∧ focProfit M α c q₀ vhat = 0) ∧
      (∀ q₀, 0 < q₀ → focProfit M α c q₀ vhat = 0 → ∀ q ∈ Set.Ici (0 : ℝ),
        (IsMaxOn (fun q' => profit M α c q' vhat) (Set.Ici 0) q ↔ q = q₀))) := by sorry

end StrategicQR.Game
