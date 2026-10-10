-- Prove2me | Theorems.Thm_SONATA_Push_lemma_I_2
-- name    : SONATA.Push.lemma_I_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:00.747058+00:00
-- url     : https://prove2.me/theorems/f1239f5f-85f8-4e65-9ff7-62d42a0ce1e4
-- title:
--   Lemma I.2, p. 47 — the weighted step length bounds the decrease of p_φ from below
-- statement:
--   In the standing setting (Assumptions A, B′, C, E, the constants (15), a solution $x^\star$), let $\alpha\in(0,1]$ and consider a run of Algorithm 3. For every $\nu$,
--   $$\alpha\sum_{i=1}^m\phi_i^\nu\|d_i^\nu\|^2\ge\frac{\mu}{D_{\rm mx}^2}\Big(p_\phi^{\nu+1}-(1-\alpha)p_\phi^\nu-\frac\alpha\mu\sum_{i=1}^m\phi_i^\nu\|\delta_i^\nu\|^2\Big),$$
--   with $D_{\rm mx}$ from (24) and $p_\phi^\nu=\sum_i\phi_i^\nu(U(x_i^\nu)-U^\star)$.
--
--   It converts the optimality gap into a lower bound on the step lengths; combined with Lemma I.1 it yields the contraction of Proposition 4.1.
--
--   **Formalization Note** The paper writes "In the setting of Lemma 3.1"; the setting is that of Lemma I.1 (Algorithm 3). The Lean states (9) multiplied through by $D_{\rm mx}^2$, i.e. $\mu\big(p_\phi^{\nu+1}-(1-\alpha)p_\phi^\nu-\frac\alpha\mu\sum_i\phi_i^\nu\|\delta_i^\nu\|^2\big)\le D_{\rm mx}^2\,\alpha\sum_i\phi_i^\nu\|d_i^\nu\|^2$. For $D_{\rm mx}>0$ this is exactly (9); at $D_{\rm mx}=0$, where the paper's division is undefined, it says the bracket is $\le 0$ (what the proof gives) rather than Lean's vacuous $\mu/0=0$.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 47, Supporting Material, Lemma I.2, (9)

import Mathlib
import Definitions.Def_SONATA_Push_Network

namespace SONATA.Push

/-- Lemma I.2 (Supporting Material, (9), p. 47):
`α Σ_i φ_i^ν ‖d_i^ν‖² ≥ (μ/D²_mx) (p_φ^{ν+1} − (1 − α) p_φ^ν − (α/μ) Σ_i φ_i^ν ‖δ_i^ν‖²)`,
stated multiplied through by `D²_mx`: `μ (p_φ^{ν+1} − (1 − α) p_φ^ν − (α/μ) Σ_i φ_i^ν ‖δ_i^ν‖²) ≤
D²_mx · α Σ_i φ_i^ν ‖d_i^ν‖²`. For `D_mx > 0` this is (9); at `D_mx = 0` it keeps the content
(the bracket is `≤ 0`) instead of Lean's `μ / 0 = 0`. -/
theorem lemma_I_2
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν : ℕ,
      μ * (pphi f G xstar (φ (ν + 1)) (x (ν + 1))
          - (1 - α) * pphi f G xstar (φ ν) (x ν)
          - α / μ * ∑ i, φ ν i * ‖delta f (x ν) (y ν) i‖ ^ 2)
        ≤ SONATA.Undir.Dmx Dl Du ^ 2 * (α * ∑ i, φ ν i * ‖dir x xh ν i‖ ^ 2) := by sorry

end SONATA.Push
