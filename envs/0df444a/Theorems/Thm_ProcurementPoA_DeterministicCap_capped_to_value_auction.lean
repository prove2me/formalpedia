-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_capped_to_value_auction
-- name    : ProcurementPoA.DeterministicCap.capped_to_value_auction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:30.416097+00:00
-- url     : https://prove2.me/theorems/f5f5cdde-96a0-4c5e-8451-13138bdc9db0
-- title:
--   Affine transport from a capped procurement equilibrium to a first-price value auction
-- statement:
--   Fix independent costs in $[1,R]$ and a no-underbidding mixed Bayes–Nash equilibrium of the procurement auction with deterministic cap $T\ge1$. There is a mixed Bayes–Nash equilibrium of a first-price value auction, with the same private types and values
--   $$v_i(c_i)=(T-c_i)_+,$$
--   whose optimal and equilibrium expected welfare equal respectively
--   $$\mathbb E[(T-C^\star)_+],\qquad
--   \mathbb E\!\left[\mathbf 1\{\min_i b_i\le T\}\,(T-c_{\mathrm{win}})\right].$$
--
--   The transport uses the affine bid map $\beta(b)=T-b$ and the tie rule obtained by reversing the order of bids. The value-auction action convention rejects negative bids. Thus bids $b>T$ are rejected in both games, bids $b=T$ map to the nonnegative bid $0$, and no special zero-bid tie priority is needed. No underbidding gives $\beta(b)\le v_i(c_i)$ on equilibrium actions. This is the affine-equivalence step that connects the capped procurement model to Jin–Lu's value-auction efficiency theorem.
--
--   **Formalization Note** The source clips bids with $(T-b)_+$ and modifies ties at zero. The present equivalent formulation leaves them unclipped and rejects precisely the resulting negative bids, as specified by `ProcurementPoA.DeterministicCap.ValueAuction`. Equalities of extended-nonnegative-real integrals record exact preservation of both welfare quantities.
-- source:
--   S. Palazzotto and A. Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission 293, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Appendix A.1.1, printed p.16 (PDF p.18), second paragraph mapping the capped procurement auction to a value auction; see also proof of Theorem 4.1, printed p.7 (PDF p.9). The unclipped map beta(b)=T-b with negative bids rejected is an equivalent action convention formalized in Definitions.Def_ProcurementPoA_DeterministicCap_ValueAuction.

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_ValueAuction

open MeasureTheory

theorem ProcurementPoA.DeterministicCap.capped_to_value_auction
    (R T : ℝ) (hR : 1 ≤ R) (hT : 1 ≤ T)
    {n : ℕ} (D : ProcurementPoA.DeterministicCap.IndependentTypes n)
    (τ : ProcurementPoA.DeterministicCap.TieRule n)
    (σ : ProcurementPoA.DeterministicCap.MixedProfile n)
    (hcost : ProcurementPoA.DeterministicCap.InCostInterval D 1 R)
    (heq : ProcurementPoA.DeterministicCap.IsBNE D τ σ T) :
    ∃ (τ' : ProcurementPoA.DeterministicCap.ValueAuction.TieRule n)
      (σ' : ProcurementPoA.DeterministicCap.MixedProfile n),
      ProcurementPoA.DeterministicCap.ValueAuction.IsBNE D τ' σ'
        (fun _ c => max (T - c) 0) ∧
      (∫⁻ c, ENNReal.ofReal
          (ProcurementPoA.DeterministicCap.ValueAuction.highest
            (fun i => max (T - c i) 0))
          ∂(ProcurementPoA.DeterministicCap.typeLaw D)) =
        ∫⁻ c, ENNReal.ofReal (T - ProcurementPoA.DeterministicCap.lowest c)
          ∂(ProcurementPoA.DeterministicCap.typeLaw D) ∧
      (∫⁻ x, ProcurementPoA.DeterministicCap.ValueAuction.welfare τ'
          (fun _ c => max (T - c) 0) x
          ∂(ProcurementPoA.DeterministicCap.playLaw D σ')) =
        ∫⁻ x, (if ProcurementPoA.DeterministicCap.lowest (fun i => (x i).2) ≤ T then
            ∑ i, ENNReal.ofReal (T - (x i).1) * τ.select (fun j => (x j).2) {i} else 0)
          ∂(ProcurementPoA.DeterministicCap.playLaw D σ) := by sorry
