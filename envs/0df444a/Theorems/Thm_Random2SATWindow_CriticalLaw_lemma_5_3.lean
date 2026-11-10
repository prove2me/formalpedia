-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_lemma_5_3
-- name    : Random2SATWindow.CriticalLaw.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:18.813883+00:00
-- url     : https://prove2.me/theorems/3c2d1643-8a11-4989-a05e-060a5e321904
-- title:
--   Lemma 5.3 — local cubic saddle: $\Psi_\gamma$ near coalescence is a generalized Airy function plus a uniform additive $O(h^{1/3})$
-- statement:
--   Fix $\gamma\in\mathbb R$. For $\tau\in\mathbb C$, $c\in\mathbb R$ and $h>0$ put $v=e^{-1}(1-\tau h^{2/3})$. As $h\downarrow0$,
--   $$\Psi_\gamma(v,h;c)=\sqrt{2\pi}\,2^{(\gamma+1)/3}h^{\gamma/3-1/6}e^{-1/(2h)+\tau/h^{1/3}+c}\big(A_\gamma(2^{1/3}\tau)+O(h^{1/3})\big),\qquad(92)$$
--   uniformly for $\tau$, $c$ in compact sets: for every $M_\tau,M_c>0$ there are $K,h_0>0$, depending only on $\gamma,M_\tau,M_c$, such that the remainder $E$ inside the parentheses has $|E|\le Kh^{1/3}$ whenever $|\tau|\le M_\tau$, $|c|\le M_c$, $0<h<h_0$; for these parameters $|v|<1$.
--
--   Differences from the source:
--   - encoding: A_γ(2^{1/3}τ) + O(h^{1/3}), additive, uniform on compacts, with the 'More precisely' constants K, h_0 → ∃ K h0 > 0, ∀ τ c h with ‖τ‖ ≤ Mτ, |c| ≤ Mc, 0 < h < h0: ‖v‖ < 1 ∧ ∃ E, ‖E‖ ≤ K h^{1/3} ∧ Ψ = prefactor · (A_γ(2^{1/3}τ) + E); reason: the paper's own quantified form; the error stays additive (A_γ may vanish)
--   - encoding: Π with any fixed c > 0 in (30), (32) → contourPi with c = 1 (rays 1 + t e^{±iπ/3}, t > 0); reason: the paper notes the value does not depend on c > 0
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Lemma 5.3, printed p. 39 (PDF 41); proof printed pp. 40–43 (PDF 42–45)

import Mathlib
import Definitions.Def_Random2SATWindow_CriticalLaw_Formulas
import Definitions.Def_Random2SATWindow_CriticalLaw_Airy
import Definitions.Def_Random2SATWindow_CriticalLaw_Hadamard
import Definitions.Def_Random2SATWindow_CriticalLaw_Strata
import Definitions.Def_Random2SATWindow_CriticalLaw_Saddle
import Definitions.Def_Random2SATWindow_CriticalLaw_PureLiteral

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace Random2SATWindow.CriticalLaw

/-- **Lemma 5.3** (local integral estimate, printed p. 39 / PDF 41). Fix `γ ∈ ℝ`. For every
`M_τ, M_c > 0` there are `K, h_0 > 0` (depending only on `γ, M_τ, M_c`) such that, for `τ ∈ ℂ`,
`c ∈ ℝ`, `h > 0` with `|τ| ≤ M_τ`, `|c| ≤ M_c`, `h < h_0` and `v = e^{-1}(1 - τ h^{2/3})`:
`|v| < 1` and
`Ψ_γ(v, h; c) = √(2π) 2^{(γ+1)/3} h^{γ/3-1/6} e^{-1/(2h) + τ/h^{1/3} + c} (A_γ(2^{1/3} τ) + E)`
with an additive remainder `|E| ≤ K h^{1/3}` (92). -/
theorem lemma_5_3 (γ Mτ Mc : ℝ) (hMτ : 0 < Mτ) (hMc : 0 < Mc) :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧
      ∀ (τ : ℂ) (c h : ℝ), ‖τ‖ ≤ Mτ → |c| ≤ Mc → 0 < h → h < h0 →
        ‖(Real.exp (-1) : ℂ) * (1 - τ * ((h ^ (2 / 3 : ℝ) : ℝ) : ℂ))‖ < 1 ∧
        ∃ E : ℂ, ‖E‖ ≤ K * h ^ (1 / 3 : ℝ) ∧
          Psi γ ((Real.exp (-1) : ℂ) * (1 - τ * ((h ^ (2 / 3 : ℝ) : ℝ) : ℂ))) h c =
            ((Real.sqrt (2 * Real.pi) * (2 : ℝ) ^ ((γ + 1) / 3) * h ^ (γ / 3 - 1 / 6) : ℝ) : ℂ) *
              Complex.exp (-1 / (2 * (h : ℂ)) + τ / ((h ^ (1 / 3 : ℝ) : ℝ) : ℂ) + c) *
              (airyA γ (((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ) * τ) + E) := by sorry

end Random2SATWindow.CriticalLaw
