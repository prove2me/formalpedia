-- Prove2me | Theorems.Thm_PayAsBid_SoftReserve_allocation_anonymous_monotone
-- name    : PayAsBid.SoftReserve.allocation_anonymous_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:48.587993+00:00
-- url     : https://prove2.me/theorems/08293b78-5385-425e-ab43-970f62a52eb6
-- title:
--   Remark closing App. A.1, p. A3 — under an equitable rule, allocations are anonymous and increase when one's own price decreases
-- statement:
--   Consider Model 2 under the standing assumptions, and let $q$ be an equitable assortment function. Write $x^q(b)=d(q(b),b)$ for its allocation. Then for every $b\in\mathbb R^n_+$:
--
--   1. allocations depend on prices and not on the identities of suppliers: for every permutation $\sigma$ of $N$,
--   $$x^q(b\circ\sigma)=x^q(b)\circ\sigma;$$
--   2. lowering supplier $i$'s price from $b_i$ to $b'\in[0,b_i)$, with the other prices fixed, weakly increases the demand allocated to $i$:
--   $$x^q_i(b)\le x^q_i(b_1,\dots,b_{i-1},b',b_{i+1},\dots,b_n).$$
--
--   These two properties are the only features of the demand model used in the proof of Lemma 4; the paper notes that Lemma 4 extends to every demand model with them.
-- source:
--   Choi, Saban & Weintraub, The Design of Optimal Pay-as-Bid Procurement Mechanisms, SSRN preprint 3785023 (version of 2022-12-08), p. A3 (PDF 36), remark after the proof of Lemma 4

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model

namespace PayAsBid.SoftReserve

theorem allocation_anonymous_monotone {n : ℕ} (P : Params n) (hP : P.Standing)
    (q : AssortFn n) (hq : IsEquitable q) :
    (∀ b : Fin n → ℝ, Nonneg b → ∀ σ : Equiv.Perm (Fin n),
      alloc P q (b ∘ σ) = alloc P q b ∘ σ) ∧
    (∀ b : Fin n → ℝ, Nonneg b → ∀ (i : Fin n) (b' : ℝ), 0 ≤ b' → b' < b i →
      alloc P q b i ≤ alloc P q (Function.update b i b') i) := by sorry

end PayAsBid.SoftReserve
