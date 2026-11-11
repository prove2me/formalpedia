-- Prove2me | Theorems.Thm_SampleMLS_ExpMoment_theorem_3_5_generating_function
-- name    : SampleMLS.ExpMoment.theorem_3_5_generating_function
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:52:06.790243+00:00
-- url     : https://prove2.me/theorems/1deb6327-4033-45a9-9822-d84650eaf408
-- title:
--   Theorem 3.5, proof — the generating-function condition: W_S(y) ≤ max_t µ_t(S)/C(n,t) · (1+y)^n, so W_S(y) ≥ (1+y)^n2^{−ψn}/Γ implies (⋆)
-- statement:
--   Let $U$ be a finite set with $n=|U|$, $S\subseteq U$ with $k=|S|$, $g$ any real function on subsets, $\psi,\Gamma$ real and $y\ge0$. Then
--   $$W_S(y)=\sum_{t=0}^{k}\binom{n}{t}y^t\frac{\mu_t(S)}{\binom{n}{t}}\le\max_{0\le t\le k}\frac{\mu_t(S)}{\binom{n}{t}}\sum_{t=0}^{n}\binom{n}{t}y^t=\max_{0\le t\le k}\frac{\mu_t(S)}{\binom{n}{t}}(1+y)^n,$$
--   so $W_S(y)\ge(1+y)^n2^{-\psi n}/\Gamma$ implies (⋆).
--
--   Differences from the source:
--   - generalization: S ∈ F_I with |S| = k, ψ ≥ 0, Γ ≥ 1, g a running-time exponent (g ≥ 0) → any S ⊆ U, any real ψ and Γ, any real g; reason: the inequality and the implication use only S ⊆ U (so C(n,t) > 0 for t ≤ k) and y ≥ 0; the source case is a special case
--   - reading: the displayed chain of equalities and inequalities → its two ends: W_S(y) ≤ max_t µ_t(S)/C(n,t) · (1 + y)^n; reason: the middle terms are the rewriting that proves it
-- source:
--   Gaspers, Monotone Local Search with Sample-Dependent Running Times, arXiv:2611.01774 (sha256 da381dca…), proof of Theorem 3.5, the generating-function condition, p. 19 (PDF 21)

import Mathlib
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_SampleMLS_ExpMoment_Model
import Definitions.Def_SampleMLS_ExpMoment_SetSystem
import Definitions.Def_SampleMLS_ExpMoment_MLS

set_option autoImplicit false

open scoped ENNReal

namespace SampleMLS.ExpMoment

/-- Proof of Theorem 3.5, the generating-function condition, p. 19 (PDF 21): for `S ⊆ U` and
`y ≥ 0`, `W_S(y) ≤ max_t µ_t(S)/(n choose t) · (1 + y)^n`, so `W_S(y) ≥ (1 + y)^n 2^{−ψn}/Γ`
implies (⋆). -/
theorem theorem_3_5_generating_function (U S : Finset ℕ) (hS : S ⊆ U) (gk : Finset ℕ → ℝ)
    (ψ Γ y : ℝ) (hy : 0 ≤ y) :
    W gk S y ≤ maxMoment gk U S * (1 + y) ^ U.card ∧
    ((1 + y) ^ U.card * (2 : ℝ) ^ (-(ψ * (U.card : ℝ))) / Γ ≤ W gk S y →
      Star gk U S ψ Γ) := by sorry

end SampleMLS.ExpMoment
