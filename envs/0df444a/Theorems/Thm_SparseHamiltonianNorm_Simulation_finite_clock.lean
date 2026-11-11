-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_finite_clock
-- name    : SparseHamiltonianNorm.Simulation.finite_clock
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:24.077381+00:00
-- url     : https://prove2.me/theorems/57e7da6e-19d0-49a7-8655-804cfb3d6357
-- title:
--   Lemma 11 — Finite-clock cross-spectral representation
-- statement:
--   For $R\ge1$, normalized complex clock amplitudes $a,b\in\mathbb C^R$, $d\ge1$, $\Lambda>0$, $t\ge0$, a finite Hermitian $M$, and an isometry $V$, the continuous routed block has the exact identity
--   $$P_{b\leftarrow a}(1)=\int_{-\pi}^{\pi}\rho_{b\leftarrow a}(\theta)\exp(-itH_\theta)\,d\theta.$$
--   The operator integrand is Bochner integrable. The spectrum is the complex cross-spectrum of the independently chosen input/output clock polynomials. Exceptional boundary phases receive the fixed extension already specified in the model.
--
--   This connects a finite sequence of routed interactions using one shared, initially empty private history to the source's boundary integral. It does not posit a nonnegative probability density or a prepared infinite catalyst.
--
--   Differences from the source:
--   - generalization: the Section 3 sparse lift → any finite Hermitian M and isometry V; reason: the routing identity and boundary formula specialize to the source lift without extra hypotheses
--   - encoding: boundary integral understood almost everywhere → an explicit finite-exception extension and an integrability conclusion; reason: assignments on the finite null set do not change the integral
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Lemma 11, p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf#page=17; printed page = PDF page; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Routing

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SparseHamiltonianNorm.Simulation
open MeasureTheory
/-- Li--Wang, Lemma 11, p.17, Eq. (58), including the original continuous history. -/
theorem finite_clock (n e d R : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (a b : Fin R → ℂ)
    (hR : 1 ≤ R) (hd : 1 ≤ d) (hΛ : 0 < Λ) (ht : 0 ≤ t)
    (hV : V.conjTranspose * V = 1) (hM : M.IsHermitian)
    (ha : clockNormSq a = 1) (hb : clockNormSq b = 1) :
    Integrable (fun θ => crossSpectrum a b θ • boundaryResponse d Λ t V M θ)
      (volume.restrict (Set.Icc (-Real.pi) Real.pi)) ∧
    clockBlock d Λ t V M 1 a b =
      ∫ θ in Set.Icc (-Real.pi) Real.pi, crossSpectrum a b θ • boundaryResponse d Λ t V M θ := by sorry
end SparseHamiltonianNorm.Simulation
