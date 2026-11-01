-- Prove2me | Theorems.Thm_RiskBalancingMNL_markup_share_inverse
-- name    : RiskBalancingMNL.markup_share_inverse
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:22.950991+00:00
-- url     : https://prove2.me/theorems/ee8e6df4-7ff4-4e87-b8c9-42d38ddc66d5
-- title:
--   Eqs (7), (8), (12) — markups and shares determine each other
-- statement:
--   Fix the MNL model with $n\ge1$ products and price coefficient $b>0$. For every markup vector $m\in\mathbb R^n$:
--
--   1. the choice probabilities (7)–(8) satisfy $q_i(m)>0$, $q_0(m)>0$ and $q_0(m)=1-\sum_iq_i(m)$;
--   2. $q_i/q_0=e^{a_i-bc_i-bm_i}$, and the markup is recovered from the shares:
--   $$
--   m_i=\frac1b\big(a_i+\log q_0-\log q_i\big)-c_i .
--   $$
--
--   For equal markups, (12) inverts the no-purchase probability: $q_0\big((\hat m(x),\dots,\hat m(x))\big)=x$ for every $x\in(0,1)$, and $\hat m\big(q_0(t,\dots,t)\big)=t$ for every $t\in\mathbb R$. Moreover $\hat m$ is strictly increasing on $(0,1)$.
--
--   This is the change of variables between markups and the no-purchase probability that the rest of §4 uses.
--
--   Differences from the source:
--   - generalization: the identities qᵢ/q₀ = e^{aᵢ−bcᵢ−bmᵢ}, mᵢ(q), q₀ = 1 − Σqᵢ and (12) → also 0 < qᵢ, 0 < q₀, both directions of the inverse (12), and strict monotonicity of m̂ on (0,1); reason: the added conclusions follow from (7), (8) and (12) and are what the page uses ("re-express m as a function of q0", "m̂(q0) is increasing"); the page's identities are among them
--   - encoding: n products → n ≥ 1; reason: with no product the threshold A = Σe^{aᵢ−bcᵢ} is 0 and (12) is undefined
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §4, p.10 (equations (7), (8) and the inverse formula) and p.11 (equation (12) and "$\hat m(q_0)$ is increasing in $q_0$")

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat

namespace RiskBalancingMNL

/-- **Eqs (7), (8), the inverse formula, and (12)**, Li & Webster, *Optimizing Risk-balancing
Return under Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14), pp.10–11. For every markup
vector `m`:
1. the shares (7)–(8) are positive and `q₀ + Σᵢ qᵢ = 1`;
2. `qᵢ/q₀ = e^{aᵢ − bcᵢ − bmᵢ}` and `mᵢ = (1/b)(aᵢ + log q₀ − log qᵢ) − cᵢ` (p.10).
For equal markups, (12) inverts the no-purchase probability: `q₀(m̂(x)) = x` for `x ∈ (0, 1)` and
`m̂(q₀(t)) = t` for every `t`; and `m̂` is strictly increasing on `(0, 1)` (p.11).

**Formalization Note** `n ≥ 1` (`NeZero n`), so that `Σᵢ e^{aᵢ − bcᵢ} > 0` and `log` in (12) is
the true logarithm. -/
theorem markup_share_inverse {n : ℕ} [NeZero n] (P : Params n) :
    (∀ m : Fin n → ℝ,
      (∀ i, 0 < share P m i) ∧ 0 < noPurchase P m ∧
      noPurchase P m + ∑ i, share P m i = 1 ∧
      (∀ i, share P m i / noPurchase P m = Real.exp (P.a i - P.b * P.c i - P.b * m i)) ∧
      ∀ i, m i = (P.a i + Real.log (noPurchase P m) - Real.log (share P m i)) / P.b - P.c i) ∧
    (∀ x : ℝ, 0 < x → x < 1 → noPurchase P (constM (mHat P x)) = x) ∧
    (∀ t : ℝ, mHat P (noPurchase P (constM t)) = t) ∧
    StrictMonoOn (mHat P) (Set.Ioo 0 1) := by sorry

end RiskBalancingMNL
