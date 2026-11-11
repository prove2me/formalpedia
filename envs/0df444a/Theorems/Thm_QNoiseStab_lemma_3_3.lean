-- Prove2me | Theorems.Thm_QNoiseStab_lemma_3_3
-- name    : QNoiseStab.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:51.079194+00:00
-- url     : https://prove2.me/theorems/c3cb8e18-d685-478f-98f3-e791dda3d8d8
-- title:
--   Lemma 3.3 — $\Pi_{B_t}\preceq(1-p)^{-t}\,T_p^A$
-- statement:
--   Let $m\ge1$, $A\subseteq[n]$ and $0\le p<1$. For every nonnegative integer $t$,
--
--   $$
--   \Pi_{B_t}\ \preceq\ (1-p)^{-t}\,T_p^A
--   $$
--
--   in the Loewner order on operators on $\mathbb C^{\mathbb Z_m^n}$, i.e. $(1-p)^{-t}T_p^A-\Pi_{B_t}$ is positive semidefinite.
--
--   This is the key comparison of the method: on low-degree states the projection is dominated by a rescaled noise operator, whose entries are classical transition probabilities.
--
--   Differences from the source:
--   - encoding: $P\preceq Q$; $(1-p)^{-t}$ → `Matrix.PosSemidef (Q - P)`; `((1 - p) ^ t)⁻¹`; reason: the Loewner order is positive semidefiniteness of the difference; $1-p>0$
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Lemma 3.3, p.12

import Mathlib
import Definitions.Def_QNoiseStab_projLowDeg
import Definitions.Def_QNoiseStab_noiseOp

open scoped ComplexOrder

namespace QNoiseStab

/-- **Lemma 3.3** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity
and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…),
p.12). For `A ⊆ [n]`, `0 ≤ p < 1`, and every nonnegative integer `t`,
`Π_{B_t} ⪯ (1 − p)^{-t} T_p^A`.

**Formalization Note** The Loewner order `P ⪯ Q` is `(Q − P).PosSemidef`. `(1 − p)^{-t}` is
`((1 − p)^t)⁻¹` (positive since `p < 1`). `t` ranges over all of `ℕ`, including `t > n`. -/
theorem lemma_3_3 {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (t : ℕ) :
    Matrix.PosSemidef (((((1 - p) ^ t)⁻¹ : ℝ) : ℂ) • (noiseOp p A : Matrix (Fin n → ZMod m)
      (Fin n → ZMod m) ℂ) - projLowDeg t) := by sorry

end QNoiseStab
