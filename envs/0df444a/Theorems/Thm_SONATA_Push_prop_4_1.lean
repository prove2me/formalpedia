-- Prove2me | Theorems.Thm_SONATA_Push_prop_4_1
-- name    : SONATA.Push.prop_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:26.024975+00:00
-- url     : https://prove2.me/theorems/acbc0086-cb2a-443b-9d6d-146ea076b712
-- title:
--   Proposition 4.1, p. 29 — p_φ contracts by σ(α) up to the weighted consensus errors
-- statement:
--   In the standing setting (Assumptions A, B′, C, E, the constants (15), a solution $x^\star$), let $\mu_i\ge0$, $L_i>0$ satisfy (1). Let $\alpha\in(0,1]$ and $\epsilon_{opt}>0$ satisfy (34):
--   $$\big(1-\tfrac\alpha2\big)\tilde\mu_{\rm mn}+\tfrac{D^\ell_{\rm mn}}2\alpha-\tfrac12\epsilon_{opt}>0 .$$
--   Then for every run of Algorithm 3 with step size $\alpha$ and every $\nu$,
--   $$p_\phi^{\nu+1}\le\sigma(\alpha)\,p_\phi^\nu+\eta(\alpha)\,\phi_{ub}\big(8L_{\rm mx}^2\|x^\nu_{\phi,\perp}\|^2+2\|y^\nu_{\phi,\perp}\|^2\big),$$
--   with $\sigma(\alpha)$, $\eta(\alpha)$ of (41)–(42). Moreover $\sigma(\alpha)<1$, $\eta(\alpha)>0$, and $\sigma(\alpha)>0$ whenever $D_{\rm mx}>0$ or $\alpha<1$.
--
--   This is the first step of the linear-rate proof: the weighted optimality gap converges linearly up to the consensus errors.
--
--   **Formalization Note** The paper states $\sigma(\alpha)\in(0,1)$ unconditionally; formula (41) gives $\sigma(\alpha)=0$ when $D_{\rm mx}=0$ and $\alpha=1$, so positivity is stated under $D_{\rm mx}>0$ or $\alpha<1$.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 29, Proposition 4.1, (80); σ, η from (41)–(42), p. 18; ε_opt from (34), p. 16; proof Supporting Material I, pp. 46–48

import Mathlib
import Definitions.Def_SONATA_Push_Network

namespace SONATA.Push

/-- Proposition 4.1 (p. 29), with `σ(α)`, `η(α)` of (41)–(42) for any `ε_opt > 0` satisfying (34):
`p_φ^{ν+1} ≤ σ(α) p_φ^ν + η(α) φ_ub (8 L²_mx ‖x_{φ,⊥}^ν‖² + 2 ‖y_{φ,⊥}^ν‖²)`, `σ(α) < 1`, `η(α) > 0`,
and `σ(α) > 0` whenever `D_mx > 0` or `α < 1` (at `D_mx = 0`, `α = 1` formula (41) gives `σ = 0`). -/
theorem prop_4_1
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (μi Li : Fin m → ℝ) (h1 : HessBounds K f μi Li)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ)
    (ε : ℝ) (hε : 0 < ε) (h34 : 0 < aCoef (SONATA.Undir.mutmn μt) (SONATA.Undir.Dlmn Dl) α ε) :
    (∀ ν : ℕ,
      pphi f G xstar (φ (ν + 1)) (x (ν + 1)) ≤
        sigma μ (SONATA.Undir.mutmn μt) (SONATA.Undir.Dlmn Dl) (SONATA.Undir.Dmx Dl Du) α ε * pphi f G xstar (φ ν) (x ν)
        + eta μ (SONATA.Undir.mutmn μt) (SONATA.Undir.Dlmn Dl) (SONATA.Undir.Dmx Dl Du) α ε * phiUb m B cl *
            (8 * SONATA.Undir.Lmx Li ^ 2 * sqn (wperp (φ ν) (x ν)) + 2 * sqn (wperp (φ ν) (y ν)))) ∧
    sigma μ (SONATA.Undir.mutmn μt) (SONATA.Undir.Dlmn Dl) (SONATA.Undir.Dmx Dl Du) α ε < 1 ∧
    0 < eta μ (SONATA.Undir.mutmn μt) (SONATA.Undir.Dlmn Dl) (SONATA.Undir.Dmx Dl Du) α ε ∧
    (0 < SONATA.Undir.Dmx Dl Du ∨ α < 1 → 0 < sigma μ (SONATA.Undir.mutmn μt) (SONATA.Undir.Dlmn Dl) (SONATA.Undir.Dmx Dl Du) α ε) := by sorry

end SONATA.Push
