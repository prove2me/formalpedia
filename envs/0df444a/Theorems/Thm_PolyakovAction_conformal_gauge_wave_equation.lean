-- Prove2me | Theorems.Thm_PolyakovAction_conformal_gauge_wave_equation
-- name    : PolyakovAction.conformal_gauge_wave_equation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T12:31:47.218707+00:00
-- url     : https://prove2.me/theorems/e86bf5ba-8145-4e63-a1fb-c51e822d0ba0
-- title:
--   Equations of motion in conformal gauge: $\Box X^\mu=0$
-- statement:
--   Work in conformal gauge with a Minkowskian target, $h_{ab}=\eta_{ab}$, $g_{\mu\nu}=\eta_{\mu\nu}=\mathrm{diag}(1,-1,\dots,-1)$, and let $T\neq0$. Let $X$ be $C^2$. If the action is stationary under every smooth compactly supported variation $X^\mu\to X^\mu+\varepsilon\,\delta X^\mu$, i.e.
--   $$\frac{d}{d\varepsilon}\Big|_{\varepsilon=0}\frac T2\int d^2\sigma\,\big(\mathcal L_P[X+\varepsilon\delta X]-\mathcal L_P[X]\big)=0,$$
--   then $X$ satisfies the wave equation
--   $$\Box X^\mu=\eta^{ab}\partial_a\partial_bX^\mu=\partial_\tau^2X^\mu-\partial_\sigma^2X^\mu=0.$$
--
--   This is the bulk equation of motion derived in the source's "Equations of motion" section.
--
--   **Formalization Note.** Variations are compactly supported, so the boundary terms of the source vanish and the variation is taken over the whole plane. The action difference is used so that the integral is finite even when $S[X]$ itself diverges.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem conformal_gauge_wave_equation {D : ℕ} (T : ℝ) (hT : T ≠ 0)
    (X : Worldsheet → Spacetime D) (hX : ContDiff ℝ 2 X)
    (hvar : ∀ δX : Worldsheet → Spacetime D, ContDiff ℝ (⊤ : ℕ∞) δX → HasCompactSupport δX →
      HasDerivAt
        (fun ε : ℝ => T / 2 * ∫ σ,
          (polyakovLagrangian (fun _ => minkowskiMetric D) (fun _ => minkowskiMetric 2)
              (fun σ' => X σ' + ε • δX σ') σ
            - polyakovLagrangian (fun _ => minkowskiMetric D) (fun _ => minkowskiMetric 2) X σ))
        0 0) :
    ∀ σ : Worldsheet, ∀ μ : Fin D,
      secondPartialDeriv X 0 0 μ σ - secondPartialDeriv X 1 1 μ σ = 0 := by sorry

end PolyakovAction
