-- Prove2me | Theorems.Thm_TorusEuler_PaperAffine_referenceModel
-- name    : TorusEuler.PaperAffine.referenceModel
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T19:40:44.205213+00:00
-- url     : https://prove2.me/theorems/c9a74512-ad62-4dff-bf0c-f2640d31b5e3
-- title:
--   Lemma 2.4 — the global Riccati reference solution and its gain
-- statement:
--   **Lemma 2.4 of the frozen manuscript (cc:lem:model).** Let $0<\varepsilon\le1$. Write $x=\varepsilon\tau^2/2$, $s=(1+x^2)^{-1/2}$, and let $\mathrm{rhs}(\varepsilon,\tau,y)=s^2(1-\varepsilon x-2\varepsilon\tau x y)-y^2$ be the reference Riccati right-hand side. There exist functions $Y,e:\mathbb{R}\to\mathbb{R}$ and a time $\tau_m$ such that:
--
--   1. $Y$ has the reference form $Y=s(1+e)-\tfrac12\varepsilon\tau x s^2$ (`referenceY`), with deviation $0\le e(\tau)\le\varepsilon/8$ for $\tau\ge0$;
--   2. $Y(0)=1$ and $Y'=\mathrm{rhs}(\varepsilon,\tau,Y)$ on $[0,\infty)$ (derivatives within $[0,\infty)$);
--   3. $|Y(\tau)|\le1$ for all $\tau\ge0$;
--   4. $Y$ has exactly one zero $\tau_m$ on $[0,\infty)$, with $2\le\varepsilon\tau_m\le3$; $Y>0$ on $[0,\tau_m)$ and $Y<0$ on $(\tau_m,\infty)$;
--   5. the logarithmic gain of the reference solution satisfies
--   $$\int_0^{\tau_m}Y(\tau)\,d\tau\ \ge\ \varepsilon^{-1/2}-1.$$
--
--   $Y$ is the logarithmic derivative $V'/V$ of the growing component of the reference amplification system; its zero locates the peak of the growth, and the integral is the logarithm of the gain achieved before the wave turns. This is the model computation behind the successive-amplification scheme.
--
--   **Formalization Note** The deviation bound is stated as `MapsTo e (Ici 0) (Icc 0 (ε/8))`; the gain bound uses $(\sqrt{\varepsilon})^{-1}-1=\varepsilon^{-1/2}-1$.
-- source:
--   Alpöge–Buckmaster–Coiculescu, *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, frozen manuscript of 18 November 2026 (torus-paper-freeze-2026-11-18). Lean: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/formalization/lean/TorusEuler/PaperAffineStatements.lean#L73; TeX: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/frozen-manuscript/sections/03_amplification.tex#L274 (cc:lem:model, cc:eq:model).

import Mathlib
import Definitions.Def_TorusEuler_Riccati

open Set
open scoped InnerProductSpace
open TorusEuler.ReferenceRiccati

namespace TorusEuler.PaperAffine

/-- Lemma 2.4, `cc:lem:model`. The global Riccati reference solution
has the stated deviation, sign, and gain, with a unique turning time. -/
theorem referenceModel {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ (Y e : ℝ → ℝ) (τm : ℝ), Y = referenceY ε e ∧ Y 0 = 1 ∧
      (∀ τ ∈ Ici 0, HasDerivWithinAt Y (rhs ε τ (Y τ)) (Ici 0) τ) ∧
      MapsTo e (Ici 0) (Icc 0 (ε / 8)) ∧ (∀ τ ∈ Ici 0, |Y τ| ≤ 1) ∧
      2 ≤ ε * τm ∧ ε * τm ≤ 3 ∧
      (∀ τ ∈ Ici 0, Y τ = 0 ↔ τ = τm) ∧
      (∀ τ ∈ Ico 0 τm, 0 < Y τ) ∧ (∀ τ ∈ Ioi τm, Y τ < 0) ∧
      (Real.sqrt ε)⁻¹ - 1 ≤ ∫ τ in 0..τm, Y τ := by sorry

end TorusEuler.PaperAffine
