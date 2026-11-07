-- Prove2me | Theorems.Thm_PrettyGoodShadow_eq_29_30_boosting
-- name    : PrettyGoodShadow.eq_29_30_boosting
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:31:18.75303+00:00
-- url     : https://prove2.me/theorems/edbcfd8a-1197-4f56-8fff-b8e42fce7881
-- title:
--   Eqs. (29)–(30) — $\mathbb E_{x\sim q}[e_q(x)]\le\frac14$ and $Z_R\le(\frac32)^R$
-- statement:
--   Let $\|O_i\|_\infty\le1$ for $i\in[m]$, $m\ge1$, and let $\varepsilon>0$, $k\ge48/\varepsilon^2$, $T\ge1$ with $2me^{-T/128}\le1/8$. Then every prior $q$ satisfies
--
--   $$
--   \mathbb E_{x\sim q}[e_q(x)]\le\frac14,
--   $$
--
--   and the boosting weights satisfy, for $Z_r=\sum_x w_r(x)$,
--
--   $$
--   Z_r\le\Big(\frac32\Big)^r .
--   $$
--
--   The first bound is the guarantee to be amplified, and the second is the potential bound of the boosting argument.
--
--   **Formalization Note** The bound on $Z_r$ is stated for every $r$.
--
--   Differences from the source:
--   - reading: k = ⌈12/ε²⌉ (p.18; "these parameters", p.31) with ∥O_i∥∞ ≤ 1 → k ≥ 48/ε²; reason: the bound at this point rests on Lemma 4.3 in the normalized form, whose threshold for ∥O∥∞ ≤ 1 is 48/ε²; k enters the theorem only through O(·)
--   - generalization: Z_R ≤ (3/2)^R for the odd number of rounds R → Z_r ≤ (3/2)^r for every r; reason: the page derives it by induction on r, and R is one case
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), eqs. (29)–(30), p.31

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_PrettyGoodShadow_failureProb

open scoped Matrix.Norms.L2Operator

namespace PrettyGoodShadow

/-- **Eqs. (29) and (30)** (arXiv:2610.06781, sha256 bd055b7d…, Appendix A, p.31). Under the parameter conditions of the
proof, every prior `q` satisfies `E_{x∼q}[e_q(x)] ≤ 1/4` (29), and the boosting weights satisfy `Z_r ≤ (3/2)^r` for
`Z_r = Σ_x w_r(x)`; in particular `Z_R ≤ (3/2)^R` (30).

**Formalization Note** The conditions are `k ≥ 48/ε²` (see `Admissible`), `T ≥ 1` and `2 m e^{−T/128} ≤ 1/8`, with
`‖O_i‖_∞ ≤ 1` as in Problem 4.1. -/
theorem eq_29_30_boosting {L d : Type} [Fintype L] [Fintype d] [DecidableEq d]
    (ρ : L → Matrix d d ℂ) (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (p : L → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (m : ℕ) (hm : 1 ≤ m) (O : Fin m → Matrix d d ℂ)
    (hOh : ∀ i, (O i).IsHermitian) (hOn : ∀ i, ‖O i‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) (k T : ℕ)
    (hk : 48 / ε ^ 2 ≤ (k : ℝ)) (hT : 1 ≤ T)
    (hTm : 2 * (m : ℝ) * Real.exp (-(T : ℝ) / 128) ≤ 1 / 8) :
    (∀ q : L → ℝ, (∀ x, 0 ≤ q x) → ∑ x, q x = 1 → ∑ x, q x * maxErr q ρ O k T ε x ≤ 1 / 4) ∧
    (∀ r : ℕ, ∑ x, wt p ρ O ε k T r x ≤ (3 / 2 : ℝ) ^ r) := by sorry

end PrettyGoodShadow
