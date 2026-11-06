-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_B_1
-- name    : UnobservedWelfare.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:48.243046+00:00
-- url     : https://prove2.me/theorems/cab3596b-4d51-47ae-a9c9-f520ddda8cda
-- title:
--   Lemma B.1 — safe delivery: $X_{ti}\le W/p_{ti}\le2A_{ti}/\kappa<A_{ti}$
-- statement:
--   Suppose $\kappa>2$ (and $0<\gamma\le1$). Fix a round $t$, a history of optimal purchases of RC buyers at strictly positive prices, and available inventory $A_t\gg0$. Define $p^I_t,p^H_t$ by (37) and post $p_t=(p^I_t+p^H_t)/2$. Then $p_t\gg0$, and every permitted purchase $X_t\in D_{\theta_t}(p_t)$ of a buyer satisfying RC at scale $W$ satisfies
--   $$X_{ti}\le\frac{W}{p_{ti}}\le\frac{2A_{ti}}{\kappa}<A_{ti}\qquad(i\in[m]).$$
--   Hence every purchase is fulfilled in full and $I_t=A_t-X_t\gg0$.
--
--   This is the inventory-safety guarantee of Algorithm 1: the inventory price alone is high enough that no buyer can exhaust the stock.
--
--   Differences from the source:
--   - generalization: conclusion about $X_t$ → the same conclusion together with $p_t\gg0$; reason: $p_t\gg0$ is proved inside the source proof (p.44) and is presupposed by the quotients $W/p_{ti}$
--   - encoding: "every valid finite history": records $(p_j,X_j)$, $j<t$, with $p_j\gg0$ and $X_j\in D_{\theta_j}(p_j)$ for RC types → records with $p_j\gg0$ and $X_j\in D(p_j)$ for buyer utilities $v_j$ satisfying RC at scale $W$; reason: a type enters the history only through its utility
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma B.1, p.43 (PDF p.45); also (38), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_gibbsMean
import Definitions.Def_UnobservedWelfare_alg1

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Lemma B.1 (safe delivery)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma B.1, p.43 (PDF p.45); also (38), p.21). Suppose
RC at scale `W` and `κ > 2`. Fix a paper round `t`, a history of optimal purchases at strictly
positive prices, and available inventory `A_t ≫ 0`; define `p^I_t`, `p^H_t` by (37) and post
`p_t = (p^I_t + p^H_t)/2`. Every permitted purchase `X_t ∈ D_{θ_t}(p_t)` then satisfies
`X_{ti} ≤ W/p_{ti} ≤ 2A_{ti}/κ < A_{ti}` for every `i`; thus every purchase is fulfilled in full and
`I_t = A_t − X_t ≫ 0`.

**Formalization Note** The history is as in `lemma_4_1`; the buyer of round `t` is any utility
satisfying the standing assumptions and RC at scale `W`. `0 < γ ≤ 1` is the parameter range fixed
with Algorithm 1 (p.20); the lemma replaces `κ ≥ 80/γ` by its own `κ > 2`. The conclusion records
`p_t ≫ 0`, which the quotients `W/p_{ti}` presuppose. -/
theorem lemma_B_1 {m : ℕ} (hm : 1 ≤ m) (T t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T) (W γ κ : ℝ)
    (hW : 0 < W) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hκ : 2 < κ)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    (rec : Fin (t - 1) → (Fin m → ℝ) × (Fin m → ℝ)) (v : Fin (t - 1) → (Fin m → ℝ) → EReal)
    (hv : ∀ j, IsBuyerUtility (v j)) (hvRC : ∀ j, IsRC W (v j))
    (hrec : ∀ j, (rec j).1 ∈ posOrthant m ∧ (rec j).2 ∈ demand (v j) (rec j).1)
    (A : Fin m → ℝ) (hA : A ∈ posOrthant m) :
    (1 / 2 : ℝ) • (inventoryPrice W γ κ (wts T t (t - 1)) rec A +
        historyPrice W c (wts T t (t - 1)) rec) ∈ posOrthant m ∧
    ∀ ut : (Fin m → ℝ) → EReal, IsBuyerUtility ut → IsRC W ut →
    ∀ X ∈ demand ut ((1 / 2 : ℝ) • (inventoryPrice W γ κ (wts T t (t - 1)) rec A +
        historyPrice W c (wts T t (t - 1)) rec)),
      (∀ i, X i ≤ W / ((1 / 2 : ℝ) • (inventoryPrice W γ κ (wts T t (t - 1)) rec A +
          historyPrice W c (wts T t (t - 1)) rec)) i ∧
        W / ((1 / 2 : ℝ) • (inventoryPrice W γ κ (wts T t (t - 1)) rec A +
          historyPrice W c (wts T t (t - 1)) rec)) i ≤ 2 * A i / κ ∧
        2 * A i / κ < A i) ∧
      A - X ∈ posOrthant m := by sorry

end UnobservedWelfare
