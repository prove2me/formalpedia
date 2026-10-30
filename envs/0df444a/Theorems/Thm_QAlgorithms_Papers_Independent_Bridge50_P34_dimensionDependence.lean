-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P34_dimensionDependence
-- name    : QAlgorithms.Papers.Independent.Bridge50.P34.dimensionDependence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:09:56.377444+00:00
-- url     : https://prove2.me/theorems/f6b7c657-2076-448d-84ae-ac3529e0fb3a
-- title:
--   Explicit entropy perturbation and logarithmic dimension order
-- statement:
--   For an integer $d\ge1$, choose a computational basis vector $|i\rangle$ and a real $\epsilon>0$ with $\epsilon d\le1$. Define
--
--   $$
--   \mu=I/d,\qquad\rho=\epsilon d|i\rangle\langle i|+(1/d-\epsilon)I.
--   $$
--
--   Then $\rho$ is a density matrix, its full trace distance from $\mu$ is $T(\mu,\rho)=2(d-1)\epsilon$, and, writing $S$ for bit entropy and $h_2$ for binary entropy in bits,
--
--   $$
--   S(\rho)\le(1-\epsilon d)\log_2d+h_2(\epsilon d),
--   $$
--   $$
--   S(\mu)-S(\rho)\ge\epsilon d\log_2d-h_2(\epsilon d)\ge\epsilon d\log_2d-1,
--   \qquad S(\mu)-S(\rho)\ge\tfrac12T(\mu,\rho)\log_2d-1.
--   $$
--
--   The logarithmic dimension order in the entanglement bounds is necessary: there exist constants $c>0$, $0<t_0\le1/e$ and an integer $d_0\ge2$, chosen before dimension, such that for every $d\ge d_0$ there are unit vectors $\psi_d,\phi_d$ on $\mathbb C^d\otimes\mathbb C^d$ satisfying
--
--   $$
--   T(\psi_d,\phi_d)\le t_0,\qquad |E(\psi_d)-E(\phi_d)|\ge c\log_2d.
--   $$
--
--   Here $E$ is marginal bit entropy, and $E_F(|\psi_d\rangle\langle\psi_d|)=E(\psi_d)$ and likewise for $\phi_d$. This records dimension-order optimality at a fixed small distance; it makes no assertion of optimal constants or distance exponents.
--
--   **Formalization Note** The positivity range makes the source's phrase “small epsilon” precise. At $d=1$ the perturbation is the unique state and the full trace distance is zero.
-- source:
--   Continuity bounds for entanglement, arXiv:quant-ph/9908086v2, PDF p. 3, Explicit entropy perturbation and logarithmic dimension dependence, (20)–(23)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P34

attribute [local instance] Classical.propDecidable Classical.decEq

-- Accepted definition providers, authorized by the independent-paper workflow.

open QAlgorithms.Papers.Independent.Information100.P08 (formation bellVector)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Support50.P42 (outcomeEntropy)

-- The supplied diagnostic timed out while elaborating the remote-control statement.

set_option maxHeartbeats 800000

/-- PDF p.3, (20)–(23): the explicit perturbation and all displayed bounds,
plus the source's dimension-order conclusion at a fixed uniformly small joint
distance. No claim of an optimal constant or distance exponent is made. -/
theorem dimensionDependence :
    (∀ (d : ℕ) (hd : 0 < d) (i : Fin d) (epsilon : ℝ),
      0 < epsilon → epsilon * d ≤ 1 →
      IsDensityMatrix (perturbedMatrix i epsilon) ∧
      fullTraceDistance (uniformMatrix d) (perturbedMatrix i epsilon) =
        2 * ((d : ℝ) - 1) * epsilon ∧
      vnEntropy (perturbedMatrix i epsilon) ≤
        (1 - epsilon * d) * Real.logb 2 d + binEntropy2 (epsilon * d) ∧
      epsilon * d * Real.logb 2 d - binEntropy2 (epsilon * d) ≤
        vnEntropy (uniformMatrix d) - vnEntropy (perturbedMatrix i epsilon) ∧
      epsilon * d * Real.logb 2 d - 1 ≤
        epsilon * d * Real.logb 2 d - binEntropy2 (epsilon * d) ∧
      fullTraceDistance (uniformMatrix d) (perturbedMatrix i epsilon) * Real.logb 2 d / 2 - 1 ≤
        vnEntropy (uniformMatrix d) - vnEntropy (perturbedMatrix i epsilon)) ∧
    (∃ (c t0 : ℝ) (d0 : ℕ), 0 < c ∧ 0 < t0 ∧ t0 ≤ 1 / Real.exp 1 ∧ 2 ≤ d0 ∧
      ∀ d : ℕ, d0 ≤ d →
      ∃ psi phi : EuclideanSpace ℂ (Fin d × Fin d), ‖psi‖ = 1 ∧ ‖phi‖ = 1 ∧
        fullTraceDistance (pureDensity psi) (pureDensity phi) ≤ t0 ∧
        c * Real.logb 2 d ≤ |vnEntropy (traceRight (pureDensity psi)) - vnEntropy (traceRight (pureDensity phi))| ∧
        formation (pureDensity psi) = vnEntropy (traceRight (pureDensity psi)) ∧
        formation (pureDensity phi) = vnEntropy (traceRight (pureDensity phi))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P34

end
