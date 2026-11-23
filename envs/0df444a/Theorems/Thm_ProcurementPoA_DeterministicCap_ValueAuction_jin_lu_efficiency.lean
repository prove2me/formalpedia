-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_ValueAuction_jin_lu_efficiency
-- name    : ProcurementPoA.DeterministicCap.ValueAuction.jin_lu_efficiency
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:33:41.18316+00:00
-- url     : https://prove2.me/theorems/dabc123e-fbaa-428f-922e-b59bf1196bfc
-- title:
--   Jin–Lu: every first-price value-auction BNE is $(1-e^{-2})$-efficient
-- statement:
--   Let $N=n+1$ bidders have independent real private types. For each bidder $i$, the value $v_i(c_i)$ is measurable and lies in $[0,V]$ on the support of her type law. Bids are independent conditional on types, satisfy no overbidding, and form a typewise mixed Bayes–Nash equilibrium of the first-price auction, with an arbitrary measurable highest-bid tie rule. Then
--
--   $$
--   (1-e^{-2})\,\mathbb E\!\left[\max_i v_i(c_i)\right]
--   \;\le\;
--   \mathbb E\!\left[\sum_i v_i(c_i)\,\mathbf 1\{i\text{ wins}\}\right].
--   $$
--
--   This is Jin–Lu's sharp $1-1/e^2$ efficiency theorem for the single-item first-price auction. Every real deviation is included in the best-response test; negative bids are simply rejected, an extension that does not change the usual nonnegative-action auction.
--
--   **Formalization Note** Values are allowed to be arbitrary measurable deterministic functions of the private type, which is equivalent to the usual independent-private-value model after pushing forward each type law. Boundedness by $V$ is a convenient specialization ensuring all displayed expectations are finite.
-- source:
--   Y. Jin and P. Lu, First Price Auction is 1−1/e² Efficient, J. ACM 70(5), 2023, doi:10.1145/3617902, Theorem 1 (every Bayes–Nash equilibrium has welfare at least $1-1/e^2$ times optimal); invoked by S. Palazzotto and A. Cristi, STOC 2027 submission 293, Appendix A.1.1, p.16 (PDF p.18).

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_ValueAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula

open MeasureTheory

theorem ProcurementPoA.DeterministicCap.ValueAuction.jin_lu_efficiency
    {n : ℕ} (D : ProcurementPoA.DeterministicCap.IndependentTypes n)
    (τ : ProcurementPoA.DeterministicCap.ValueAuction.TieRule n)
    (σ : ProcurementPoA.DeterministicCap.MixedProfile n) (V : ℝ)
    (v : ProcurementPoA.DeterministicCap.Suppliers n → ℝ → ℝ) (hV : 0 ≤ V)
    (hvmeas : ∀ i, Measurable (v i))
    (hv : ∀ i, ∀ c ∈ D.types i, v i c ∈ Set.Icc 0 V)
    (heq : ProcurementPoA.DeterministicCap.ValueAuction.IsBNE D τ σ v) :
    ENNReal.ofReal (1 - ProcurementPoA.DeterministicCap.epsilon) *
        ∫⁻ c, ENNReal.ofReal (ProcurementPoA.DeterministicCap.ValueAuction.highest
          (fun i => v i (c i))) ∂(ProcurementPoA.DeterministicCap.typeLaw D) ≤
      ∫⁻ x, ProcurementPoA.DeterministicCap.ValueAuction.welfare τ v x
        ∂(ProcurementPoA.DeterministicCap.playLaw D σ) := by sorry
