-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_convex_envelope_reduction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.convex_envelope_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:58:05.921728+00:00
-- url     : https://prove2.me/theorems/b901c855-d0dd-4bda-bde3-126ac68127dc
-- title:
--   Isotropic entanglement is the scalar convex envelope
-- statement:
--   Let $d\ge2$ and $D=[1/d,1]$. Define $q_d(x)$ as the minimum of $2(1-\sum_k\mu_k^2)$ over probabilities $\mu_k\ge0$, $\sum_k\mu_k=1$, satisfying $\sum_k\sqrt{\mu_k}=\sqrt{dx}$, and set $c_d=\sqrt{q_d}$. For $g=q_d$ or $c_d$ define
--
--   $$
--   H_g(F)=\min\left\{\sum_jp_jg(x_j):\ p_j\ge0,\ \sum_jp_j=1,\ x_j\in D,\ \sum_jp_jx_j=F\right\}.
--   $$
--
--   Each minimum is over all finite ensembles and is attained. The function $H_g$ is the greatest convex function on $D$ bounded above by $g$. For the explicit isotropic density $\rho_{d,F}=FP_d+(1-F)(I-P_d)/(d^2-1)$, where $P_d=|\Phi_d\rangle\langle\Phi_d|$,
--
--   $$
--   \tau(\rho_{d,F})=H_{q_d}(F),\qquad C(\rho_{d,F})=H_{c_d}(F)\quad(F\in D).
--   $$
--
--   For each cost there is a normalized finite pure ensemble with average cost equal to this value whose density twirls to $\rho_{d,F}$. The twirl integrates conjugation by $U\otimes\overline U$ against probability Haar measure. For $0\le F\le1/d$, both roofs vanish.
--
--   This is the complete reduction from isotropic mixed states to one scalar profile and its convex envelope.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 7, §3.2, (3.14)–(3.17): isotropic convex-envelope reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, (3.14)--(3.17): isotropic roofs equal the full scalar convex
envelopes; scalar ensemble minima attain. Below separability both roofs vanish.
The input state is the explicit isotropicDensityAtFidelity matrix, not a hypothesized twirl. -/
theorem convex_envelope_reduction (d : ℕ) (hd : 2 ≤ d) :
    IsConvexEnvelope (Set.Icc (1 / (d : ℝ)) 1) (constrainedSchmidtTangle d) (scalarConvexRoofAtFidelity d (constrainedSchmidtTangle d)) ∧
    IsConvexEnvelope (Set.Icc (1 / (d : ℝ)) 1) (rawC d) (scalarConvexRoofAtFidelity d (rawC d)) ∧
    (∀ F ∈ Set.Icc (1 / (d : ℝ)) 1,
      tangle (isotropicDensityAtFidelity d F) = scalarConvexRoofAtFidelity d (constrainedSchmidtTangle d) F ∧
      concurrence (isotropicDensityAtFidelity d F) = scalarConvexRoofAtFidelity d (rawC d) F ∧
      IsLeast (hullValues d (constrainedSchmidtTangle d) F) (scalarConvexRoofAtFidelity d (constrainedSchmidtTangle d) F) ∧
      IsLeast (hullValues d (rawC d) F) (scalarConvexRoofAtFidelity d (rawC d) F) ∧
      (∃ e : PureEnsemble (Fin d × Fin d),
        (∑ k, e.weight k * pureTangle (e.vector k)) = scalarConvexRoofAtFidelity d (constrainedSchmidtTangle d) F ∧
        Bridge50.P37.bipartiteHaarTwirl d true (ensembleDensity e.weight e.vector) = isotropicDensityAtFidelity d F) ∧
      (∃ e : PureEnsemble (Fin d × Fin d),
        (∑ k, e.weight k * pureConcurrence (e.vector k)) = scalarConvexRoofAtFidelity d (rawC d) F ∧
        Bridge50.P37.bipartiteHaarTwirl d true (ensembleDensity e.weight e.vector) = isotropicDensityAtFidelity d F)) ∧
    (∀ F ∈ Set.Icc (0 : ℝ) (1 / (d : ℝ)),
      tangle (isotropicDensityAtFidelity d F) = 0 ∧ concurrence (isotropicDensityAtFidelity d F) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
