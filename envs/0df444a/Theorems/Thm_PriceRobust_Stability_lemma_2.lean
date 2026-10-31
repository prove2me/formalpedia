-- Prove2me | Theorems.Thm_PriceRobust_Stability_lemma_2
-- name    : PriceRobust.Stability.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:12.759664+00:00
-- url     : https://prove2.me/theorems/a73223dc-a884-4e90-b967-dc9da19f9e0d
-- title:
--   Lemma 2, p. 15 — a firm's robust best response moves by at most R_{N(i),N(i)}⁻¹ times the change in its intercept α
-- statement:
--   Consider the market of §3 with $a\ge 0$, Assumptions (P), (Z), (IS), and $w\in\mathbb R^{\mathcal N}_{++}$. Fix price vectors $\hat p,\tilde p\ge 0$, let $\check p=\min\{\hat p,\tilde p\}$ (componentwise), and fix a firm $i$. Let
--   $$\hat\alpha=a_{\mathcal N(i)}-R_{\mathcal N(i),-\mathcal N(i)}\hat p_{-\mathcal N(i)},$$
--   and define $\tilde\alpha,\check\alpha$ likewise from $\tilde p,\check p$. Let $\hat p^*,\tilde p^*,\check p^*$ be firm $i$'s robust best responses to $\hat p,\tilde p,\check p$. Then
--   $$0\le \hat p^*-\check p^*\le R^{-1}_{\mathcal N(i),\mathcal N(i)}(\hat\alpha-\check\alpha),\qquad 0\le \tilde p^*-\check p^*\le R^{-1}_{\mathcal N(i),\mathcal N(i)}(\tilde\alpha-\check\alpha).$$
--
--   This comparison is the per-firm estimate from which the componentwise contraction bound of Theorem 3 is assembled. The paper's proof (Online Appendix D) uses Theorem 4(b) and Lemma B.2(d) of Federgruen and Hu (2016), which are not proved in this paper.
--
--   **Formalization Note** The robust best responses are taken as full vectors $\hat q,\tilde q,\check q$ with $\hat q=RB(\hat p)$ etc., and the inequalities are stated for the coordinates of firm $i$. $\check\alpha$ is defined from $\check p$, as $a_{\mathcal N(i)}-R_{\mathcal N(i),-\mathcal N(i)}\check p_{-\mathcal N(i)}$, matching the page's definition $\check p^*=RB_i(\check p_{-\mathcal N(i)})$. The page also writes $\check\alpha=\min\{\hat\alpha,\tilde\alpha\}$; that identity does not hold in general and is not used: (Z) gives only $\check\alpha\le\min\{\hat\alpha,\tilde\alpha\}$, with strict inequality when firm $i$ faces two competitor products priced in opposite order under $\hat p$ and $\tilde p$. Read with $\min\{\hat\alpha,\tilde\alpha\}$ in place of $\check\alpha$, (18) would fail in such a case.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), p. 15 (PDF 16), Lemma 2, eq. (18)

import Mathlib
import Definitions.Def_PriceRobust_Stability_Model

open Matrix

namespace PriceRobust.Stability

theorem lemma_2 {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (w : ι → ℝ) (hw : ∀ l, 0 < w l)
    (phat ptil : ι → ℝ) (hphat : 0 ≤ phat) (hptil : 0 ≤ ptil)
    (qhat qtil qchk : ι → ℝ)
    (hqhat : M.IsRobustBR w phat qhat) (hqtil : M.IsRobustBR w ptil qtil)
    (hqchk : M.IsRobustBR w (fun l => min (phat l) (ptil l)) qchk) (i : F) :
    let pchk : ι → ℝ := fun l => min (phat l) (ptil l)
    let αhat := M.blockAlpha i phat
    let αtil := M.blockAlpha i ptil
    let αchk := M.blockAlpha i pchk
    ∀ (l : ι) (hl : M.firm l = i),
      (0 ≤ qhat l - qchk l ∧
        qhat l - qchk l ≤
          ((M.Rblock i)⁻¹ *ᵥ (fun k : {l // M.firm l = i} => αhat k.1 - αchk k.1)) ⟨l, hl⟩) ∧
      (0 ≤ qtil l - qchk l ∧
        qtil l - qchk l ≤
          ((M.Rblock i)⁻¹ *ᵥ (fun k : {l // M.firm l = i} => αtil k.1 - αchk k.1)) ⟨l, hl⟩) := by sorry

end PriceRobust.Stability
