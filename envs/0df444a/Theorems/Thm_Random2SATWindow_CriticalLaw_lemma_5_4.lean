-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_lemma_5_4
-- name    : Random2SATWindow.CriticalLaw.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:17.558203+00:00
-- url     : https://prove2.me/theorems/1dc10fed-c950-4679-a626-5f4838cb6079
-- title:
--   Lemma 5.4 — uniform separated-saddle estimate for $\Psi_\gamma$, relative error $O(\sqrt{h/\kappa^3})$
-- statement:
--   Fix $\gamma$ and a bounded set of real $c$. Write $T_0=T(v)$, $D=1-T_0$ and $\kappa=1-|T_0|>0$. On any family with $|v|\le e^{-1}$ and $|D|\le C\kappa$,
--   $$\Psi_\gamma(v,h;c)=e^{-U(v)/h}D^{\gamma-1/2}e^{cT_0}\Big(1+O\big(\sqrt{h/\kappa^3}\big)\Big)\qquad(108)$$
--   provided $h/\kappa^3$ is sufficiently small; all constants are uniform on this family. Read with explicit constants: for every $\gamma$, $M_c>0$ and $C>0$ there are $\varepsilon_0,K>0$ such that for all $v\in\mathbb C$, $c\in\mathbb R$, $h>0$ with $|v|\le e^{-1}$, $|c|\le M_c$, $\kappa>0$, $|D|\le C\kappa$ and $h/\kappa^3\le\varepsilon_0$, the relative error $E$ satisfies $|E|\le K\sqrt{h/\kappa^3}$ ($D^{\gamma-1/2}$ principal, $\operatorname{Re}D>0$).
--
--   Differences from the source:
--   - reading: 'on any family with |v| ≤ e^{-1} and |D| ≤ Cκ … provided h/κ³ is sufficiently small. All constants are uniform on this family' → ∀ γ Mc C > 0, ∃ ε0 K > 0, ∀ v c h, ‖v‖ ≤ e^{-1} → |c| ≤ Mc → 0 < κ → ‖D‖ ≤ Cκ → 0 < h → h/κ³ ≤ ε0 → ∃ E, ‖E‖ ≤ K √(h/κ³) ∧ Ψ = e^{-U/h} D^{γ-1/2} e^{cT_0}(1 + E); reason: the loosely quantified family statement pinned to its uniform reading (one ε0, K for the whole family {|v| ≤ e^{-1}, |D| ≤ Cκ}), the stronger of the possible readings
--   - encoding: a bounded set of real c → |c| ≤ Mc for an arbitrary Mc > 0; reason: every bounded set of reals lies in some [−Mc, Mc]
--   - encoding: T(v), the solution of T = v e^T with T(0) = 0, extended continuously to |v| ≤ e^{-1} → treeT v = Σ_{m ≥ 1} m^{m−1} v^m / m! (its Lagrange series, given by the paper); reason: the series converges absolutely on the closed disk and equals the continuous extension there
--   - encoding: Ψ_γ(v, h; c) for h > 0 (88) → hypothesis 0 < h; reason: Ψ_γ is only defined for h > 0 (factor 1/√(2πh) and e^{-t²/(2h)})
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Lemma 5.4, printed p. 43 (PDF 45); proof printed pp. 43–45 (PDF 45–47)

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

/-- **Lemma 5.4** (uniform separated-saddle estimate, printed p. 43 / PDF 45), in the pinned
reading of "on any family … provided `h/κ³` is sufficiently small; all constants are uniform".
Fix `γ`, a bound `M_c` for the real parameter `c`, and the family constant `C > 0`. There are
`ε_0, K > 0` such that for every `v` with `|v| ≤ e^{-1}`, writing `T_0 = T(v)`, `D = 1 - T_0`,
`κ = 1 - |T_0|`, whenever `κ > 0`, `|D| ≤ Cκ`, `|c| ≤ M_c`, `h > 0` and `h/κ³ ≤ ε_0`:
`Ψ_γ(v, h; c) = e^{-U(v)/h} D^{γ-1/2} e^{c T_0} (1 + E)` with `|E| ≤ K √(h/κ³)` (108)
(principal power `D^{γ-1/2}`). -/
theorem lemma_5_4 (γ Mc C : ℝ) (hMc : 0 < Mc) (hC : 0 < C) :
    ∃ ε0 K : ℝ, 0 < ε0 ∧ 0 < K ∧
      ∀ (v : ℂ) (c h : ℝ), ‖v‖ ≤ Real.exp (-1) → |c| ≤ Mc →
        0 < 1 - ‖treeT v‖ → ‖1 - treeT v‖ ≤ C * (1 - ‖treeT v‖) → 0 < h →
        h / (1 - ‖treeT v‖) ^ 3 ≤ ε0 →
        ∃ E : ℂ, ‖E‖ ≤ K * Real.sqrt (h / (1 - ‖treeT v‖) ^ 3) ∧
          Psi γ v h c = Complex.exp (-treeU v / h) * (1 - treeT v) ^ ((γ - 1 / 2 : ℝ) : ℂ) *
            Complex.exp (c * treeT v) * (1 + E) := by sorry

end Random2SATWindow.CriticalLaw
