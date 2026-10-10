-- Prove2me | Theorems.Thm_SONATA_Push_lemma_I_1
-- name    : SONATA.Push.lemma_I_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:16:40.762086+00:00
-- url     : https://prove2.me/theorems/c77cb68a-98f4-4492-84a8-92e5c44a4f03
-- title:
--   Lemma I.1, p. 46 — the local step decreases U up to α‖d_i‖‖δ_i‖
-- statement:
--   In the standing setting (Assumptions A, B′, C, E, the constants (15), a solution $x^\star$), let $\alpha\in(0,1]$ and consider a run of Algorithm 3. For every agent $i$ and every $\nu$,
--   $$U(x_i^{\nu+\frac12})\le U(x_i^\nu)-\alpha\Big(\big(1-\tfrac\alpha2\big)\tilde\mu_i+\tfrac\alpha2D^\ell_i\Big)\|d_i^\nu\|^2+\alpha\|d_i^\nu\|\,\|\delta_i^\nu\|,$$
--   where $d_i^\nu=\hat x_i^\nu-x_i^\nu$, $x_i^{\nu+1/2}=x_i^\nu+\alpha d_i^\nu$ and $\delta_i^\nu=\nabla F(x_i^\nu)-y_i^\nu$.
--
--   The local surrogate step decreases the objective up to a term driven by the tracking error; this is the per-agent descent inequality of the analysis.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 46, Supporting Material, Lemma I.1, (1)

import Mathlib
import Definitions.Def_SONATA_Push_Network

namespace SONATA.Push

/-- Lemma I.1 (Supporting Material, (1), p. 46):
`U(x_i^{ν+1/2}) ≤ U(x_i^ν) − α((1 − α/2) μ̃_i + (α/2) D^ℓ_i) ‖d_i^ν‖² + α ‖d_i^ν‖ ‖δ_i^ν‖`. -/
theorem lemma_I_1
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν : ℕ, ∀ i : Fin m,
      U f G (xhalf α x xh ν i) ≤ U f G (x ν i)
        - α * ((1 - α / 2) * μt i + α / 2 * Dl i) * ‖dir x xh ν i‖ ^ 2
        + α * ‖dir x xh ν i‖ * ‖delta f (x ν) (y ν) i‖ := by sorry

end SONATA.Push
