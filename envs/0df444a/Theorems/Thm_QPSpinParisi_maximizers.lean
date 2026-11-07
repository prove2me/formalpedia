-- Prove2me | Theorems.Thm_QPSpinParisi_maximizers
-- name    : QPSpinParisi.maximizers
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:19:15.23728+00:00
-- url     : https://prove2.me/theorems/6eb6a3d7-e118-4092-9f79-c63b2681fe34
-- title:
--   p.24 — a maximizing control exists, and it equals $\nabla\Phi$ along its own path
-- statement:
--   Fix $\gamma\in\mathcal U$ and $\Phi=\Psi_{\xi,\gamma}$. The supremum defining $\Psi_{\xi,\gamma}(0,0)$ in (2.3) is attained at a control in $D[0,1]$. For each maximizer $u$, with $X^u_t=\int_0^t\sqrt{\zeta}\,dB+\int_0^t\zeta\gamma u$, and each $0\le a<b<1$ with $\gamma(a)>0$,
--   $$u(t)=\nabla\Phi(t,X^u_t)\qquad\text{for almost every }t\in[a,b],\text{ almost surely.}$$
--   This is the characterization of maximizers used in the proof of strict convexity.
--
--   Differences from the source:
--   - generalization: one Brownian motion $B$ on an unnamed space → every `BrownianNoise`, on every probability space; reason: the source's $B$ is one such object, and `exists_noise` makes the statement non-vacuous
--   - reading: "$t\in[a,b]$" with $a,b$ never introduced → $0\le a<b<1$ with $\gamma(a)>0$, and almost every $t$; reason: where $\gamma=0$ the objective of (2.3) does not see $u$, and neither does it on a null set of times, so the identity could not hold there
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.24 (PDF p.24); p.19 (PDF p.19)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_USet
import Definitions.Def_QPSpinParisi_gradPsi
import Definitions.Def_QPSpinParisi_Dctrl
import Definitions.Def_QPSpinParisi_BrownianNoise_noise

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.24, PDF p.24: "The characterization of maximizers in [Che25, Proposition 3.2] gives `u(t) = ∇Φ_j(t, X^j_t) = ∇Φ_λ(t, X^λ_t)`,
`t ∈ [a, b]`"; and p.19, PDF p.19: "the maximizing control lies in `D[s, 1]`". For `γ ∈ U` the supremum in (2.3) at `(0, 0)` is attained, and each maximizer `u` satisfies
`u(t) = ∇Φ(t, X^u_t)` along its own path `X^u_t = ∫₀ᵗ √ζ dB + ∫₀ᵗ ζ γ u`.

**Formalization Note** The source never introduces `a, b`. The identity is read for `a < b < 1` with `γ(a) > 0` (which gives `0 ≤ a`), for almost every `t ∈ [a, b]`: where `γ` vanishes the
objective does not see `u`, and on a null set of times neither does it, so the identity would fail there. -/
theorem maximizers (c : ℕ → ℝ) (hc : MixHyp c) (W : BrownianNoise c) (γ : Ico (0 : ℝ) 1 → ℝ) (hγ : γ ∈ USet) :
    (∃ u ∈ Dctrl W 0, ctrlJ W (fun y => ‖y‖) (fun r => zeta c r * gamHat γ r) 0 0 u = Psi W γ 0 0) ∧
    ∀ u ∈ Dctrl W 0, ctrlJ W (fun y => ‖y‖) (fun r => zeta c r * gamHat γ r) 0 0 u = Psi W γ 0 0 →
      ∀ a b : ℝ, a < b → b < 1 → 0 < gamHat γ a →
        ∀ᵐ t ∂(volume.restrict (Icc a b)), ∀ᵐ ω ∂W.P,
          u t.toNNReal ω = gradPsi W γ t (W.noise t.toNNReal ω +
            ∫ r in (0 : ℝ)..t, (zeta c r * gamHat γ r) • u r.toNNReal ω) := by sorry

end QPSpinParisi
