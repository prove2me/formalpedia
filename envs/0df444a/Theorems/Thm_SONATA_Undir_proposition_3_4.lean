-- Prove2me | Theorems.Thm_SONATA_Undir_proposition_3_4
-- name    : SONATA.Undir.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:42.851274+00:00
-- url     : https://prove2.me/theorems/3bc4acdd-b2d7-4b69-b63d-17758782903b
-- title:
--   Proposition 3.4, p. 18 — p^{ν+1} ≤ σ(α)p^ν + η(α)(4L²_mx‖x_⊥^ν‖² + 2‖y_⊥^ν‖²), σ(α) < 1, η(α) > 0
-- statement:
--   Under the standing assumptions of §3.3 and constants $L_i$ as in (1), let $(\mathbf x^\nu,\mathbf y^\nu,\hat{\mathbf x}^\nu)$ be a run of SONATA with step size $\alpha\in(0,1]$, and let $\varepsilon_{\rm opt}$ satisfy (34): $\varepsilon_{\rm opt}>0$ and $\big(1-\frac\alpha2\big)\tilde\mu_{\rm mn}+\frac{\alpha D^\ell_{\rm mn}}2-\frac12\varepsilon_{\rm opt}>0$. With $\sigma(\alpha)$, $\eta(\alpha)$ as in (41)–(42):
--
--   1. for every $\nu$,
--   $$p^{\nu+1}\le\sigma(\alpha)\,p^\nu+\eta(\alpha)\big(4L_{\rm mx}^2\|\mathbf x_\perp^\nu\|^2+2\|\mathbf y_\perp^\nu\|^2\big);$$
--   2. $\sigma(\alpha)<1$ and $\eta(\alpha)>0$;
--   3. if $D_{\rm mx}>0$ or $\alpha<1$, then $\sigma(\alpha)>0$.
--
--   The optimality gap contracts linearly up to the consensus errors. It is the first link of the chain of Proposition 3.8.
--
--   **Formalization Note.** The page states $\sigma(\alpha)\in(0,1)$ unconditionally, but (41) gives $\sigma(\alpha)=0$ when $D_{\rm mx}=0$ and $\alpha=1$; positivity is therefore stated under the disjunction $D_{\rm mx}>0$ or $\alpha<1$. The inequality and $\sigma(\alpha)<1$, $\eta(\alpha)>0$ are stated without it.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 18, Proposition 3.4, (40)–(42), with (34) p. 16

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting
import Definitions.Def_SONATA_Undir_Chain

namespace SONATA.Undir

theorem proposition_3_4
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    {μi Li : Fin m → ℝ} (h1 : Eq1 K f μi Li)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x y xh : ℕ → Stack m d}
    (hrun : IsRun K f G ft W α x y xh) :
    ∀ εopt : ℝ, Cond34 (mutmn μt) (Dlmn Dl) α εopt →
      (∀ ν, pgap f G xstar x (ν + 1) ≤
          sigmaA μ (mutmn μt) (Dlmn Dl) (Dmx Dl Du) α εopt * pgap f G xstar x ν
            + etaA μ (mutmn μt) (Dlmn Dl) (Dmx Dl Du) α εopt
              * (4 * Lmx Li ^ 2 * stackNormSq (perp (x ν)) + 2 * stackNormSq (perp (y ν)))) ∧
      sigmaA μ (mutmn μt) (Dlmn Dl) (Dmx Dl Du) α εopt < 1 ∧
      0 < etaA μ (mutmn μt) (Dlmn Dl) (Dmx Dl Du) α εopt ∧
      ((0 < Dmx Dl Du ∨ α < 1) → 0 < sigmaA μ (mutmn μt) (Dlmn Dl) (Dmx Dl Du) α εopt) := by sorry

end SONATA.Undir
