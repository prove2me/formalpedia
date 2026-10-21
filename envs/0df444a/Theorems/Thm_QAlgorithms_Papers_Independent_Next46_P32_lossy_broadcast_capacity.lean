-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P32_lossy_broadcast_capacity
-- name    : QAlgorithms.Papers.Independent.Next46.P32.lossy_broadcast_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:30:56.742485+00:00
-- url     : https://prove2.me/theorems/ddd91473-acd2-4582-aad7-cf290c626882
-- title:
--   Capacity with additional vacuum loss
-- statement:
--   The channel acts on the full countable Fock space with independent fixed vacuum environment modes. Messages are independent and uniform on finite nonempty sets, arbitrary block density operators are allowed, and the receivers use separate POVMs. Let $\mathcal C$ denote the convex hull of the closure of achievable nonnegative rate pairs, measured in nats per use, using vanishing maximal joint error: Bob decodes both messages and Charlie decodes his own. The energy constraint is unconditional, averaged over messages and uses, with total block expectation at most $n\bar N$. Write $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$.
--
--   Let $0\le\eta_C<\eta_B$, $\eta_B+\eta_C<1$, and $\bar N\ge0$. Construct the channel by attenuating the input with intensity $\eta_B+\eta_C$ against vacuum, then splitting the retained field with Bob fraction $\eta_B/(\eta_B+\eta_C)$. For every normalized full-Fock block input, Charlie's reduced state equals Bob's reduced state attenuated against vacuum with intensity $\eta_C/\eta_B$. Assuming global Strong Conjecture 2, the capacity region is
--
--   $$
--   \mathcal C=\bigcup_{0\le\beta\le1}\{(R_B,R_C)\ge0:
--   R_B\le g(\eta_B\beta\bar N),\quad
--   R_C\le g(\eta_C\bar N)-g(\eta_C\beta\bar N)\}.
--   $$
--
--   The zero-coupling endpoint $\eta_C=0$ is retained and forces $R_C=0$. This is a specified vacuum-loss network, not an arbitrary noisy channel with the same coefficients.
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, PDF p. 4, Section IV, unnumbered unequal-coupling extension

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity productCoeff)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section IV, PDF p.4: vacuum loss followed by splitting, with strictly
unequal receiver intensities. etaC=0 is included. -/
theorem lossy_broadcast_capacity (etaB etaC Nbar : ℝ)
    (hC : 0 ≤ etaC) (hBC : etaC < etaB) (hloss : etaB + etaC < 1)
    (hNbar : 0 ≤ Nbar) (hconj : StrongConjecture2) :
    (∀ (n : ℕ), 0 < n → ∀ rho : State (NumberString n),
      charlieMarginal (lossyBroadcast n etaB etaC rho.coefficients) =
        pureLoss n (etaC / etaB)
          (bobMarginal (lossyBroadcast n etaB etaC rho.coefficients))) ∧
    sourceRegion (fun n => lossyBroadcast n etaB etaC) Nbar =
      thermalRegion etaB etaC Nbar := by sorry

end QAlgorithms.Papers.Independent.Next46.P32

end
