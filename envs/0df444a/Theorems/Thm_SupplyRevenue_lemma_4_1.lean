-- Prove2me | Theorems.Thm_SupplyRevenue_lemma_4_1
-- name    : SupplyRevenue.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:16.161158+00:00
-- url     : https://prove2.me/theorems/adf22876-96be-4c2b-9d63-31e50c58e1b0
-- title:
--   Lemma 4.1 — XOS surplus retention
-- statement:
--   Let $v$ be XOS with clauses $B_v$ and $q\ge 0$. Then
--
--   $$U_v(T,q)=\max_{b\in B_v}\sum_{j\in T}(b_j-q_j)_+ .$$
--
--   If $S$ is a random stock whose items each survive with probability at least $1-\eta$, and $W=U_v(J,q)$, $Y=U_v(J\cap S,q)$, then
--
--   $$0\le Y\le W,\qquad EY\ge(1-\eta)W,\qquad E\min\{Y,z\}\ge(1-\eta)\min\{W,z\}\quad(z\ge 0).\tag{6}$$
--
--   The items of $S$ may be correlated. These are the retention bounds used by Lemma 4.2.
--
--   Differences from the source:
--   - encoding: random stock $S$ → a mass function on bundles; reason: the stock is finite-valued
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Lemma 4.1, p.8, (6)

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model
import Definitions.Def_SupplyRevenue_Local

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Lemma 4.1, p.8 (XOS surplus retention), with (6).

**Formalization Note** The clauses of `E` are the set `B_v`. Prices `q ≥ 0` (p.8: stock and prices of §4). The stock is any
mass function on bundles with item survival `≥ 1 − η`, and its indicators may be correlated. `J` is an arbitrary bundle.
-/
theorem lemma_4_1 {m : ℕ} (E : ComplementFreeCA.XOSGreedy.XOSExpr m) (q : Fin m → ℝ)
    (hq : ∀ j, 0 ≤ q j) :
    (∀ T, surplus E.val T q =
      E.clauses.sup' E.nonempty fun b => ∑ j ∈ T, max (b j - q j) 0) ∧
    ∀ (J : Finset (Fin m)) (μ : Lottery m) (η : ℝ), GoodStock μ η →
      let W := surplus E.val J q
      let Y : Finset (Fin m) → ℝ := fun S => surplus E.val (J ∩ S) q
      (∀ S, 0 ≤ Y S ∧ Y S ≤ W) ∧
      (1 - η) * W ≤ μ.E Y ∧
      ∀ z : ℝ, 0 ≤ z → (1 - η) * min W z ≤ μ.E fun S => min (Y S) z := by sorry

end SupplyRevenue
