-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P54_fock_counting
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P54.fock_counting
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:09:30.43233+00:00
-- url     : https://prove2.me/theorems/6762a349-3e25-4b44-ae0f-1721c436d558
-- title:
--   Optimal Fock photon counting and total-count threshold
-- statement:
--   Let $M\ge1$ be the finite number of signal modes and $J\ge0$ the finite number of retained idler modes, on the full optical Fock spaces. The two channels have equal priors, independent vacuum environments, reflectances $0\le R_0\le R_1\le1$, field magnitudes $r_b=\sqrt{R_b}$ and $t_b=\sqrt{1-R_b}$, and distinct complex reflection coefficients $r_b e^{i\theta_b}$. Every signal mode sees the same channel; idlers are retained losslessly and environment outputs are inaccessible. Write $\mathcal F$ for squared Uhlmann fidelity, $P_e$ for minimum average error over all joint binary receivers, $Q_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$, and $Q=\min_{0\le s\le1}Q_s$, with zero powers interpreted as support projections. Here the common phase is removed, so $\theta_0=\theta_1=0$ and $R_0<R_1$. Put $\mu=r_0r_1+t_0t_1$.
--
--   For a multimode Fock input $|\mathbf N\rangle$ with total photon number $K$, the returned states are diagonal and commute. The observed occupation $\mathbf j$ has conditional law
--
--   $$\Pr_b(\mathbf j)=\prod_m\binom{N_m}{j_m}R_b^{j_m}(1-R_b)^{N_m-j_m},\quad0\le j_m\le N_m,$$
--
--   and zero otherwise. Its total $T=\sum_mj_m$ has the binomial law $B_b(T)=\binom KT R_b^T(1-R_b)^{K-T}$. Photon counting followed by the likelihood decision, assigning equality to one, attains
--
--   $$P_e=\frac12\sum_{T=0}^K\min\{B_0(T),B_1(T)\}.$$
--
--   For $0<R_0<R_1<1$ and possible counts $T\le K$, the likelihood ratio is at least one exactly when
--
--   $$T\ge K\frac{\ln[(1-R_0)/(1-R_1)]}{\ln[R_1(1-R_0)/(R_0(1-R_1))]}.$$
--
--   The optimum depends only on $K$, independently of occupations and mode count; $K=0$ gives a tie and error $1/2$.
-- source:
--   Discriminating quantum-optical beam-splitter channels with number-diagonal signal states: Applications to quantum reading and target detection, arXiv:1105.4063v3, PDF p. 8, fock-counting

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P54

noncomputable section

open scoped BigOperators ComplexConjugate

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P54

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Photon counting is optimal and depends only on total Fock photon number,
PDF p.8, (62)–(65). j counts observed photons, whereas source k counts losses.
The logarithmic likelihood rule is restricted to strict interior reflectances. -/
theorem fock_counting {M : ℕ} (hM : 0 < M) (c : Channels)
    (hc : ValidSplitters c) (hr : Reading c) (n : Occupation (Fin M)) :
    (∀ b x y, returned (c b) (fock n) x y =
      if x=y then (countLaw (c b) n x.2 : ℂ) else 0) ∧
    kernelProduct (returned (c false) (fock n)) (returned (c true) (fock n)) =
      kernelProduct (returned (c true) (fock n)) (returned (c false) (fock n)) ∧
    (∀ b j, (∑' q : Occupation (Fin M), if photons q=j then countLaw (c b) n q else 0) =
      totalCountLaw (c b) (photons n) j) ∧
    outputError c (fock n) = countingError c (photons n) ∧
    (∃ E, IsOpticalEffect E ∧ CountsAs E (fun q => decide
      (totalCountLaw (c false) (photons n) (photons q) ≤
        totalCountLaw (c true) (photons n) (photons q))) ∧
      sectorRisk c (fock n) E (1/2) (1/2)=outputError c (fock n)) ∧
    (0 < (c false).reflectance → (c true).reflectance < 1 →
      ∀ j : ℕ, j ≤ photons n →
        ((1 ≤ ((c true).reflectance^j * (1-(c true).reflectance)^(photons n-j)) /
          ((c false).reflectance^j * (1-(c false).reflectance)^(photons n-j))) ↔
        countThreshold c (photons n) ≤ (j : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P54

end
