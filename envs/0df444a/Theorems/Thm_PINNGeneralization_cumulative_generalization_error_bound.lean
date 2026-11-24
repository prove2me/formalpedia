-- Prove2me | Theorems.Thm_PINNGeneralization_cumulative_generalization_error_bound
-- name    : PINNGeneralization.cumulative_generalization_error_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:46:29.63571+00:00
-- url     : https://prove2.me/theorems/624d2a84-ec89-444e-9af5-1f493dfd0381
-- title:
--   Lemma 2.10: cumulative generalization error for random training points
-- statement:
--   Let the abstract PDE of Section 2.1 be posed on $\mathbb D=[0,1]^{\bar d}$ with $Y=L^1(\mathbb D;\mathbb R^m)$, and let $u\in X^*$ be its solution. For each training set $\mathbb S=(y_1,\dots,y_N)\in\mathbb D^N$, $N\ge1$, let $u^*(\mathbb S)\in X^*$ be the trained network, with residual $\mathcal R(\cdot;\mathbb S)=\mathcal D(u^*(\mathbb S))-f$. Training sets are drawn from $d\mathbb S=dy^{\otimes N}$. Assume there is a constant $C_{pde}>0$ with
--
--   $$\|u-u^*(\mathbb S)\|_X\le C_{pde}\,\|\mathcal D(u)-\mathcal D(u^*(\mathbb S))\|_{L^1(\mathbb D)}\quad\text{for every }\mathbb S.$$
--
--   Assume also that $\mathbb S\mapsto\|u-u^*(\mathbb S)\|_X$ is measurable, that $(\mathbb S,z)\mapsto|\mathcal R(z;\mathbb S)|$ is integrable on $\mathbb D^N\times\mathbb D$, that each $\mathbb S\mapsto|\mathcal R(y_n;\mathbb S)|$ is integrable, and that $z\mapsto\int|\mathcal R(z;\mathbb S)|\,d\mathbb S$ is square integrable on $\mathbb D$. Let the validation points $z_1,\dots,z_N$ be independent and uniformly distributed on $\mathbb D$. Then
--
--   $$\bar{\mathcal E}_G\le C_{pde}\Big(\bar{\mathcal E}_T+\mathcal E_{TV}+\frac{\mathrm{std}(|\mathcal R|)}{\sqrt N}\Big),$$
--
--   with the cumulative errors $\bar{\mathcal E}_G$, $\bar{\mathcal E}_T$, the validation gap $\mathcal E_{TV}=\mathbb E|\bar{\mathcal E}_T-\bar{\mathcal E}_V|$ and the standard deviation $\mathrm{std}(|\mathcal R|)$ of eqs. (2.24)-(2.30).
--
--   The lemma replaces the deterministic quadrature bound by a Monte Carlo bound on an independent validation set.
--
--   **Formalization Note** The map $\mathbb S\mapsto u^*(\mathbb S)$ is arbitrary. The integrability and measurability hypotheses are implicit in the paper, which treats all these integrals as finite. $\mathrm{std}$ is written as an integral over $\mathbb D$ rather than as an expectation over one uniform random point, which is the same quantity.
-- source:
--   Mishra and Molinaro, Estimates on the generalization error of Physics Informed Neural Networks (PINNs) for approximating PDEs, arXiv:2006.16144v3 (2023), Section 2.4.1, Lemma 2.10, eqs. (2.24)-(2.30), p. 10

import Mathlib
import Definitions.Def_PINNGeneralization_Basic

open MeasureTheory

namespace PINNGeneralization

theorem cumulative_generalization_error_bound {n m N : ℕ} {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (P : AbstractPDE n m X) (hP : P.Hyp) (hdom : P.dom = unitCube n) (hp : P.p = 1)
    (hN : 0 < N) (u : X) (hu : P.IsSolution u)
    (ustar : (Fin N → Pt n) → X) (hustar : ∀ S, ustar S ∈ P.Xs)
    (Cpde : ℝ) (hC : 0 < Cpde)
    (hstab : ∀ S, ‖u - ustar S‖ ≤ Cpde * lpNorm P.dom P.p (P.D u - P.D (ustar S)))
    (hmeas : AEStronglyMeasurable (fun S => ‖u - ustar S‖) (trainLaw n N))
    (hRint : Integrable (fun q : (Fin N → Pt n) × Pt n => ‖P.residual (ustar q.1) q.2‖)
      ((trainLaw n N).prod (volume.restrict (unitCube n))))
    (hRtr : ∀ j, Integrable (fun S => ‖P.residual (ustar S) (S j)‖) (trainLaw n N))
    (hRsq : MemLp (fun z => ∫ S, ‖P.residual (ustar S) z‖ ∂trainLaw n N) 2
      (volume.restrict (unitCube n)))
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (zval : Fin N → Ω → Pt n) (hzm : ∀ j, Measurable (zval j))
    (hind : ProbabilityTheory.iIndepFun zval Pr)
    (hlaw : ∀ j, Pr.map (zval j) = volume.restrict (unitCube n)) :
    cumGenError u ustar ≤
      Cpde * (cumTrainError (fun S => P.residual (ustar S)) +
        validationGap Pr (fun S => P.residual (ustar S)) zval +
        residualStd (fun S => P.residual (ustar S)) / Real.sqrt N) := by sorry

end PINNGeneralization
