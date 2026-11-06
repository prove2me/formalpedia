-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_4_1
-- name    : UnobservedWelfare.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:49.538525+00:00
-- url     : https://prove2.me/theorems/89e40039-e57e-4f3a-9917-71d926ea5bf6
-- title:
--   Lemma 4.1 — production optimality (40) and production budget (41)
-- statement:
--   Let $1\le t\le T$, let $(p_j,X_j)_{j<t}$ be a valid history (strictly positive prices, optimal purchases of RC buyers) and let $I_{t-1}\ge0$. Then the production problem of Algorithm 1,
--   $$\min_{v\in[0,1]^m}\{c(v)+\Phi_{w_t}(I_{t-1}+v)\},$$
--   has a unique minimizer $q_t$, with $A_t=I_{t-1}+q_t\gg0$, and
--   $$c(q_t)+c^*(p^I_t)=p^I_t\cdot q_t,\tag{40}$$
--   $$c(q_t)+2c^*(p_t)\le(\kappa+2)mW+\frac{\gamma WM_t}{2},\tag{41}$$
--   where $p^I_t$ is the inventory price at $A_t$ and $p_t=(p^I_t+p^H_t)/2$.
--
--   Production is thus profit-maximizing at the inventory price, and the production cost plus the posted-price profit stays bounded.
--
--   Differences from the source:
--   - encoding: "every valid finite history": records $(p_j,X_j)$, $j<t$, with $p_j\gg0$ and $X_j\in D_{\theta_j}(p_j)$ for RC types → records with $p_j\gg0$ and $X_j\in D(p_j)$ for buyer utilities $v_j$ satisfying RC at scale $W$; reason: a type enters the history only through its utility
--   - encoding: $\Phi_w(A)=+\infty$ when $A$ has a zero coordinate → `invPotential` is `EReal`-valued, $\top$ off $\mathbb R^m_{++}$; reason: exact $+\infty$ value, so no junk real value can make a boundary inventory optimal
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 4.1, (40), (41), p.23 (PDF p.25)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_gibbsMean
import Definitions.Def_UnobservedWelfare_alg1

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Lemma 4.1 (production optimality)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 4.1, (40), (41), p.23 (PDF p.25)). For
every valid finite history of paper round `t` and `I_{t−1} ≥ 0`, the production problem of
Algorithm 1, `min_{v ∈ [0,1]^m} {c(v) + Φ_{w_t}(I_{t−1} + v)}`, has a unique minimizer `q_t`, with
`A_t = I_{t−1} + q_t ≫ 0`, and `c(q_t) + c*(p^I_t) = p^I_t · q_t` (40). Moreover
`c(q_t) + 2c*(p_t) ≤ (κ + 2)mW + γWM_t/2` (41), where `p_t = (p^I_t + p^H_t)/2`.

**Formalization Note** A valid history is a list of records `(p_j, X_j)`, `j < t`, with `p_j ≫ 0`
and `X_j ∈ D_{θ_j}(p_j)` for buyer utilities `v j` satisfying RC at scale `W`. The weights are the
schedule weights `w_t` of paper round `t`. `Φ = +∞` off `ℝ^m_{++}` (`invPotential`). -/
theorem lemma_4_1 {m : ℕ} (hm : 1 ≤ m) (T t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T) (W γ κ : ℝ)
    (hW : 0 < W) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hκ : 80 / γ ≤ κ)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    (rec : Fin (t - 1) → (Fin m → ℝ) × (Fin m → ℝ)) (v : Fin (t - 1) → (Fin m → ℝ) → EReal)
    (hv : ∀ j, IsBuyerUtility (v j)) (hvRC : ∀ j, IsRC W (v j))
    (hrec : ∀ j, (rec j).1 ∈ posOrthant m ∧ (rec j).2 ∈ demand (v j) (rec j).1)
    (I : Fin m → ℝ) (hI : 0 ≤ I) :
    (∃! q, IsProdMin W γ κ c (wts T t (t - 1)) rec I q) ∧
    ∀ q, IsProdMin W γ κ c (wts T t (t - 1)) rec I q →
      I + q ∈ posOrthant m ∧
      c q + costConj c (inventoryPrice W γ κ (wts T t (t - 1)) rec (I + q)) =
        inventoryPrice W γ κ (wts T t (t - 1)) rec (I + q) ⬝ᵥ q ∧
      c q + 2 * costConj c ((1 / 2 : ℝ) • (inventoryPrice W γ κ (wts T t (t - 1)) rec (I + q) +
          historyPrice W c (wts T t (t - 1)) rec)) ≤
        (κ + 2) * m * W + γ * W * mass T t / 2 := by sorry

end UnobservedWelfare
