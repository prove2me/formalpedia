-- Prove2me | Theorems.Thm_PayAsBid_SoftReserve_demand_antitone_assortment
-- name    : PayAsBid.SoftReserve.demand_antitone_assortment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:04.61131+00:00
-- url     : https://prove2.me/theorems/bc269d27-b141-4163-9ebc-1aada656defc
-- title:
--   Proof of Lemma 4, step (9), p. A3 — enlarging the assortment weakly lowers each included supplier's demand
-- statement:
--   Consider Model 2 under the standing assumptions. Let $Q\subseteq Q'$ be assortments, $i\in Q$, and $p\in\mathbb R^n_+$. Then supplier $i$'s demand is weakly smaller in the larger assortment:
--
--   $$d_i(Q',p)\le d_i(Q,p).$$
--
--   In the proof of Lemma 4 this is why a supplier that is in the assortment under both an equitable rule $q^*$ and the no-competition rule receives at least as much demand under $q^*$, which may exclude other suppliers: inequality (9).
-- source:
--   Choi, Saban & Weintraub, The Design of Optimal Pay-as-Bid Procurement Mechanisms, SSRN preprint 3785023 (version of 2022-12-08), p. A3 (PDF 36), proof of Lemma 4, justification of (9)

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model

namespace PayAsBid.SoftReserve

theorem demand_antitone_assortment {n : ℕ} (P : Params n) (hP : P.Standing)
    (Q Q' : Finset (Fin n)) (i : Fin n) (hi : i ∈ Q) (hQQ' : Q ⊆ Q')
    (p : Fin n → ℝ) (hp : Nonneg p) :
    demand P Q' p i ≤ demand P Q p i := by sorry

end PayAsBid.SoftReserve
