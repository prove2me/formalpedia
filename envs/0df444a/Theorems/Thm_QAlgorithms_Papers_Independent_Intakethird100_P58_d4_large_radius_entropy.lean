-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P58_d4_large_radius_entropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P58.d4_large_radius_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:59:48.288095+00:00
-- url     : https://prove2.me/theorems/d0034ad9-9fbf-4d07-8188-e99863d8c2b7
-- title:
--   Large-ball reduced entropy and its exact constant-term integral
-- statement:
--   Fix the positive D4 scales and $N_c\ge1$ as above. There exist $\rho_{\min}>0$ and regular cylinder profiles $r_\rho(z)$ for every $\rho\ge\rho_{\min}$, anchored by $r_\rho(0)=\rho$. Let $g$ be the explicit regular coefficient (4.23), put $q(z)=-(1+z)/(1+z+z^2)=g'(z)$, and define
--
--   $$
--   H(z)=\frac{4g(z)+z(1-z^3)q(z)^2}{2z^3}.
--   $$
--
--   For every fixed regulator $0<a<1$, $H$ is integrable on $[a,1]$ and the actual reduced entropy satisfies
--
--   $$
--   S(\rho,a)=K\int_a^1\left[\frac{\rho^2}{z^3}+H(z)\right]dz+O(\rho^{-1})\qquad(\rho\to\infty).
--   $$
--
--   Here $K=\pi^3R_{\mathrm{curv}}^6U_0R_4/(2G_N^{(10)})$ is the chosen reduced prefactor, $S_{\rho^2}=K\rho^2\int_a^1z^{-3}dz$, and $\gamma(a)=-K\int_a^1H(z)dz$. The error constant and threshold may depend on the fixed regulator and model, and precede $\rho$.
--
--   The result constructs a stationary cylinder family and its area asymptotics without assuming them. It gives the integral coefficient before the disputed evaluations (4.25)/(4.28), and does not exchange the fixed-cutoff and large-radius limits.
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, PDF p. 20, (4.24)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory

open scoped Topology

/-- PDF pp.19--20, (4.24): construct the large-boundary-radius D4 cylinder
family and the constant-term integral of its actual reduced regulatedAction. First fix
0<a<1, then take rho to infinity. Neither a profile expansion nor the resulting
area estimate is assumed. This is the integral coefficient, not (4.25)/(4.28). -/
theorem d4_large_radius_entropy (P : D4Parameters) (N : ℕ) (hN : 0 < N) :
    ∃ (rhoMin : ℝ) (C : ℝ → ℝ → ℝ), 0 < rhoMin ∧
      (∀ rho : ℝ, rhoMin ≤ rho → IsCylinder .d4 rho (C rho)) ∧
      ∀ a : ℝ, 0 < a → a < 1 →
        IntervalIntegrable d4ConstantDensity volume a 1 ∧
        ∃ B M : ℝ, 0 < B ∧ rhoMin ≤ M ∧
          ∀ rho : ℝ, M ≤ rho →
            |d4Entropy P N (C rho) a 1 - d4Prefactor P N *
              (rho ^ 2 * (∫ z in a..(1 : ℝ), 1 / z ^ 3) +
                ∫ z in a..(1 : ℝ), d4ConstantDensity z)| ≤ B / rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P58

end
