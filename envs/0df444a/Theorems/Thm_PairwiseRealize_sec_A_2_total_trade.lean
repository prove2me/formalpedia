-- Prove2me | Theorems.Thm_PairwiseRealize_sec_A_2_total_trade
-- name    : PairwiseRealize.sec_A_2_total_trade
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:55:42.422198+00:00
-- url     : https://prove2.me/theorems/1cbbbb87-85bb-49dc-9a1f-2c49ec63dab1
-- title:
--   §A.2, p.11 — the three-row total trade
-- statement:
--   For $n\ge2$ and $\tau\in V$, compare the two rows $\tau\oplus e_1,\tau\oplus e_2$ with the single row $\tau\oplus e_1\oplus e_2$. The difference $w_{\tau\oplus e_1}+w_{\tau\oplus e_2}-w_{\tau\oplus e_1\oplus e_2}$ equals $1$ on the total, $\tau_i$ on every singleton $i$, and has absolute value at most $1$ on every pair.
--
--   These trades correct the total count, at a bounded cost to the other statistics.
--
--   Differences from the source:
--   - reading: e₁, e₂ are basis vectors of V, n unrestricted → the first two coordinates, with n ≥ 2; reason: the trade needs two coordinates; Theorem 2.1 is for large n
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.2, p.11 (PDF p.12); §3.1, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_PairwiseRealize_Model

namespace PairwiseRealize

/-- **The three-row total trade, §A.2 p.11 (PDF p.12); §3.1 p.6 (PDF p.7).** K. Shi, H. Sun,
*Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission (manuscript sha256
62090516…): "let eᵢ denote the ith standard basis vector of V and use independent uniform
translations {τ ⊕ e1, τ ⊕ e2} versus {τ ⊕ (e1 ⊕ e2)}, τ ∈ V. […] The total difference is one; the
singleton difference is τᵢ; every pair difference has absolute value at most one."

For `n ≥ 2` and every `τ ∈ V`, the difference `w_{τ⊕e₁} + w_{τ⊕e₂} − w_{τ⊕e₁⊕e₂}` is `1` on the
total, `τᵢ` on every singleton `i`, and has absolute value at most `1` on every pair.

**Formalization Note** `e₁, e₂` are the first two coordinates, `Fin` indices `0` and `1`;
`τ ⊕ eᵢ` flips coordinate `i` of `τ`. -/
theorem sec_A_2_total_trade (n : ℕ) (hn : 2 ≤ n) (τ : Row n) :
    let i₁ : Fin n := ⟨0, by omega⟩
    let i₂ : Fin n := ⟨1, by omega⟩
    let flip : Row n → Fin n → Row n := fun x i => Function.update x i (!x i)
    let Δ : Feat n → ℤ := fun f =>
      wvec n (flip τ i₁) f + wvec n (flip τ i₂) f - wvec n (flip (flip τ i₁) i₂) f
    Δ Feat.total = 1 ∧ (∀ i, Δ (Feat.single i) = bv (τ i)) ∧
      ∀ i j (h : i < j), |Δ (Feat.pair i j h)| ≤ 1 := by sorry

end PairwiseRealize
