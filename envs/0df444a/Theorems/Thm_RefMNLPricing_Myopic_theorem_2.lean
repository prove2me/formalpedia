-- Prove2me | Theorems.Thm_RefMNLPricing_Myopic_theorem_2
-- name    : RefMNLPricing.Myopic.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:59.065331+00:00
-- url     : https://prove2.me/theorems/76290d13-1b34-447d-9ca0-f0de3667dac6
-- title:
--   Theorem 2, p. 13 — the myopic price equals Π^m(r) plus a type- and threshold-dependent constant
-- statement:
--   Consider the MNL pricing model with reference effects, with $b_i>0$, $c_i^\pm\ge 0$, price box $\mathcal P^n=[0,p_H]^n$, $p_H>0$, and assume the ceiling assumption $p_H \ge \hat p_H$ (some solution of (9) is at most $p_H$). Let $r\in\mathcal P^n$, let $p^m$ be any maximiser of $\Pi(\cdot,r)$ over $\mathcal P^n$, and let $\Pi^m := \Pi(p^m,r)$ be the optimal single-period revenue. Then for every product $i$:
--
--   1. If $i$ is loss-averse ($c_i^+<c_i^-$),
--   $$
--   p_i^m = \begin{cases} \Pi^m + \frac{1}{b_i+c_i^-}, & r_i < \Pi^m + \frac{1}{b_i+c_i^-},\\[1mm] \Pi^m + \frac{1}{b_i+c_i^+}, & r_i > \Pi^m + \frac{1}{b_i+c_i^+},\\[1mm] r_i, & \Pi^m + \frac{1}{b_i+c_i^-} \le r_i \le \Pi^m + \frac{1}{b_i+c_i^+}. \end{cases}
--   $$
--   2. If $i$ is loss-neutral ($c_i^+ = c_i^- =: c_i$), $p_i^m = \Pi^m + \frac{1}{b_i+c_i}$.
--   3. If $i$ is gain-seeking ($c_i^+>c_i^-$), then with $Z_i = \frac{\log(b_i+c_i^+)-\log(b_i+c_i^-)}{c_i^+-c_i^-}$ one has $Z_i\in\big[\frac{1}{b_i+c_i^+},\frac{1}{b_i+c_i^-}\big]$, and
--   $$
--   p_i^m = \begin{cases} \Pi^m + \frac{1}{b_i+c_i^-}, & r_i < \Pi^m + Z_i,\\[1mm] \Pi^m + \frac{1}{b_i+c_i^+}, & r_i > \Pi^m + Z_i, \end{cases}
--   $$
--   while at the threshold $r_i = \Pi^m + Z_i$ the price $p_i^m$ is one of these two values.
--
--   Together with Theorem 1, this reduces the $n$-dimensional myopic problem to computing one number, $\Pi^m(r)$.
--
--   **Formalization Note** The paper prints (16) with "$r_i \ge \Pi^m+Z_i$" in the second case. At the threshold both candidate prices attain the maximum (e.g. $(a,b,c^+,c^-)=(1,1,2,1)$, $r=0.87462$: both give revenue $0.469150$), so the printed $\ge$ is a tie-break; the statement covers every maximiser and therefore claims only "one of the two" at the threshold. The statement holds for every maximiser, not a chosen one. The ceiling assumption is necessary: with a binding ceiling the maximiser can sit on the boundary of the box.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 13, Theorem 2, (14)–(16); standing assumption §2.4, p. 11

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model
import Definitions.Def_RefMNLPricing_Myopic_Equation13

namespace RefMNLPricing.Myopic

/-- Theorem 2, p. 13. Under the standing assumptions and the ceiling assumption `p_H ≥ p̂_H`, let
`r ∈ Pⁿ` and let `p` be any maximiser of `Π(·, r)` over `Pⁿ`, with optimal revenue
`Π^m = Π(p, r)`. Then for every product `i`:
* loss-averse (`c_i⁺ < c_i⁻`), (14): `p_i = Π^m + 1/(b_i+c_i⁻)` if `r_i < Π^m + 1/(b_i+c_i⁻)`,
  `p_i = Π^m + 1/(b_i+c_i⁺)` if `r_i > Π^m + 1/(b_i+c_i⁺)`, and `p_i = r_i` otherwise;
* loss-neutral (`c_i⁺ = c_i⁻`), (15): `p_i = Π^m + 1/(b_i+c_i⁺)`;
* gain-seeking (`c_i⁻ < c_i⁺`), (16): `Z_i ∈ [1/(b_i+c_i⁺), 1/(b_i+c_i⁻)]`;
  `p_i = Π^m + 1/(b_i+c_i⁻)` if `r_i < Π^m + Z_i`, `p_i = Π^m + 1/(b_i+c_i⁺)` if
  `r_i > Π^m + Z_i`, and at the threshold `r_i = Π^m + Z_i` the price is one of the two (both are
  attained by some maximiser; the printed `≥` is a tie-break). -/
theorem theorem_2 {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH)
    (r p : Fin n → ℝ) (hr : InBox pH r) (hp : IsBoxMax a b cp cm pH r p) :
    ∀ i : Fin n,
      (cp i < cm i →
        (r i < revenue a b cp cm p r + 1 / (b i + cm i) →
          p i = revenue a b cp cm p r + 1 / (b i + cm i)) ∧
        (revenue a b cp cm p r + 1 / (b i + cp i) < r i →
          p i = revenue a b cp cm p r + 1 / (b i + cp i)) ∧
        (revenue a b cp cm p r + 1 / (b i + cm i) ≤ r i →
          r i ≤ revenue a b cp cm p r + 1 / (b i + cp i) → p i = r i)) ∧
      (cp i = cm i → p i = revenue a b cp cm p r + 1 / (b i + cp i)) ∧
      (cm i < cp i →
        (1 / (b i + cp i) ≤ Zgap b cp cm i ∧ Zgap b cp cm i ≤ 1 / (b i + cm i)) ∧
        (r i < revenue a b cp cm p r + Zgap b cp cm i →
          p i = revenue a b cp cm p r + 1 / (b i + cm i)) ∧
        (revenue a b cp cm p r + Zgap b cp cm i < r i →
          p i = revenue a b cp cm p r + 1 / (b i + cp i)) ∧
        (r i = revenue a b cp cm p r + Zgap b cp cm i →
          p i = revenue a b cp cm p r + 1 / (b i + cm i) ∨
            p i = revenue a b cp cm p r + 1 / (b i + cp i))) := by sorry

end RefMNLPricing.Myopic
