-- Prove2me | Theorems.Thm_ViscosityPPDE_Comparison_lemma_6_3
-- name    : ViscosityPPDE.Comparison.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:29:35.95874+00:00
-- url     : https://prove2.me/theorems/b7403efe-3b61-4094-b07f-6da0655c9649
-- title:
--   Lemma 6.3 — the ODE solution $u^{t,\omega}$ of (6.8) is a classical solution on $\Lambda^t$
-- statement:
--   Let Assumptions 4.2 and 4.4 hold, with $\hat f$ the extension of Assumption 4.4. Let $t<T$, let $\theta\in(C^0_b(\Lambda^t))^d$ satisfy (6.5) with extension $\hat\theta$, let $z\in\mathbb R^d$, $x\in\mathbb R$ and $\omega\in\Omega$, and let $\hat Z$, $\hat v$ be given by (6.7). Let $\hat u^{t,\omega}$ solve the ODE with random coefficients
--   $$\hat u^{t,\omega}(s,\hat\omega) = x - \int_t^s\hat f^{t,\omega}\big(r,\hat\omega,\hat u^{t,\omega}(r,\hat\omega),\hat Z_r(\hat\omega)\big)\,dr + \hat v(s,\hat\omega),\qquad t\le s\le T,\ \hat\omega\in\hat\Omega^t,\qquad(6.8)$$
--   where $\hat f^{t,\omega}(r,\hat\omega,y,z) = \hat f(r,\omega\otimes_t\hat\omega,y,z)$, and let $u^{t,\omega} = \hat u^{t,\omega}$ on $\Lambda^t$ (6.9). Then $u^{t,\omega}\in C^{1,2}_b(\Lambda^t)$ and
--   $$(\mathcal L^{t,\omega}u^{t,\omega})(s,\tilde\omega) = 0\qquad\text{for all }(s,\tilde\omega)\in[t,T)\times\Omega^t.$$
--
--   These classical solutions with a piecewise-affine-in-time gradient are the building blocks from which the proof of Theorem 6.1 assembles elements of $\overline{\mathcal D}$ and $\underline{\mathcal D}$ close to $u^0$.
--
--   **Formalization Note** The page assumes only Assumption 4.2 and (6.5), but (6.8) is built from $\hat f$, which exists only under Assumption 4.4; that assumption is added (a printed slip). The lemma quantifies over every $\hat u^{t,\omega}$ solving (6.8) pathwise on $\hat\Omega^t$, with the integrand integrable on $[t,s]$, instead of "the unique solution". The operator identity is required for every $C^{1,2}_b(\hat\Lambda^t)$ extension of $u^{t,\omega}$; on $\Lambda^t$, $\hat f^{t,\omega} = f^{t,\omega}$ by Assumption 4.4(i).
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, (6.5)–(6.9), Lemma 6.3, pp. 25–26

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Viscosity
import Definitions.Def_ViscosityPPDE_Comparison_Standing
import Definitions.Def_ViscosityPPDE_Comparison_Approx

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

theorem lemma_6_3 {d : ℕ} {T : ℝ≥0} (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ)
    (g : Omega d T 0 → ℝ) (L0 : ℝ) (h42 : Assumption42 f g L0)
    (fhat : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ → Rd d → ℝ) (h44 : Assumption44 f fhat)
    (t : ℝ≥0) (htT : t < T) (θ : ℝ≥0 → Omega d T t → Rd d)
    (θhat : ℝ≥0 → (ℝ≥0 → Rd d) → Rd d) (h65 : Cond65 T t θ θhat) (z : Rd d) (x : ℝ)
    (ω : Omega d T 0) (uhat : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ)
    (hode : ∀ s ω', t ≤ s → s ≤ T → ω' ∈ OmegaHatSet d T t →
      IntegrableOn (fun r : ℝ => fhat r.toNNReal (concatHat ω t ω') (uhat r.toNNReal ω')
        (Zhat t z θhat r.toNNReal ω')) (Set.Icc (t : ℝ) s) ∧
      uhat s ω' = x - (∫ r in Set.Icc (t : ℝ) s, fhat r.toNNReal (concatHat ω t ω')
        (uhat r.toNNReal ω') (Zhat t z θhat r.toNNReal ω')) + vhat t z θhat s ω') :
    (∃ X, ExtC12b T t (fun s (ω' : Omega d T t) => uhat s ω'.1) X) ∧
      ∀ X, ExtC12b T t (fun s (ω' : Omega d T t) => uhat s ω'.1) X →
        ∀ s (ω' : Omega d T t), t ≤ s → s < T →
          shiftedOp f t ω X s ω'.1 ω' (uhat s ω'.1) = 0 := by sorry

end ViscosityPPDE.Comparison
