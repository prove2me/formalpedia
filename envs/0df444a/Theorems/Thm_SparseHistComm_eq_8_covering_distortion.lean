-- Prove2me | Theorems.Thm_SparseHistComm_eq_8_covering_distortion
-- name    : SparseHistComm.eq_8_covering_distortion
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:18.227445+00:00
-- url     : https://prove2.me/theorems/f31626e3-2bec-4531-ae49-f8788de97b84
-- title:
--   Eq. (8) — covering distortion $\|\hat u - u\|_1 \le k - \frac1n\sum_i J_i$, so $\sum_i J_i \ge nk - \lfloor nD\rfloor$ gives distortion $\le D$
-- statement:
--   Let $n \ge 1$, $1 \le k \le d$, $d \ge 2$, $0 \le D < k$, let $x_1,\dots,x_n$ be binary inputs with $\|x_i\|_0 \le k$ and empirical histogram $u$, let each user select a covering level $J_i \in \{0,\dots,k\}$ and keep exactly $\min\{J_i, \|x_i\|_0\}$ active coordinates of its input, giving $y_i$ with $\mathrm{supp}(y_i) \subseteq \mathrm{supp}(x_i)$, and let $\hat u = \frac1n\sum_i y_i$. Then
--   $$
--   \|\hat u - u\|_1 = \Big\|\frac1n\sum_{i=1}^n (x_i - y_i)\Big\|_1 = \frac1n\sum_{i=1}^n \|x_i - y_i\|_1 \le \frac1n\sum_{i=1}^n (k - J_i) = k - \frac1n\sum_{i=1}^n J_i , \tag{8}
--   $$
--   and consequently $\|\hat u - u\|_1 \le D$ whenever $\sum_{i=1}^n J_i \ge nk - \lfloor nD\rfloor$.
--
--   This is the distortion guarantee of the randomized covering scheme that yields the upper bound (13).
--
--   Differences from the source:
--   - encoding: binary vectors xᵢ ∈ {0,1}^d with ‖xᵢ‖₀ ≤ k → supports xᵢ : Finset (Fin d) with card ≤ k; reason: bijection, ‖xᵢ‖₀ = card
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section III, Eq. (8) and the preceding paragraph, p.6

import Mathlib
import Definitions.Def_SparseHistComm_Admissible
import Definitions.Def_SparseHistComm_ind
import Definitions.Def_SparseHistComm_empHist
import Definitions.Def_SparseHistComm_l1
import Definitions.Def_SparseHistComm_threshold

namespace SparseHistComm

/-- **Eq. (8) and its consequence** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section III, p.6). Let `x` be admissible, let each user
select a covering level `Jᵢ ∈ {0, …, k}` and keep exactly `min{Jᵢ, ‖xᵢ‖₀}` active coordinates of
its input, `yᵢ ⊆ xᵢ`, and let `û = (1/n)∑ᵢ yᵢ`. Then
`‖û − u‖₁ = ‖(1/n)∑ᵢ(xᵢ − yᵢ)‖₁ = (1/n)∑ᵢ‖xᵢ − yᵢ‖₁ ≤ (1/n)∑ᵢ(k − Jᵢ) = k − (1/n)∑ᵢ Jᵢ`,
and consequently `‖û − u‖₁ ≤ D` whenever `∑ᵢ Jᵢ ≥ nk − ⌊nD⌋`.

**Formalization Note** The reproduction `û` is `empHist y`; `‖xᵢ − yᵢ‖₁` is the `ℓ₁` distance of
the indicator vectors. -/
theorem eq_8_covering_distortion (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (D : ℝ) (hD0 : 0 ≤ D) (hDk : D < k)
    (x : Fin n → Finset (Fin d)) (hx : Admissible k x) (J : Fin n → ℕ) (hJ : ∀ i, J i ≤ k)
    (y : Fin n → Finset (Fin d)) (hyx : ∀ i, y i ⊆ x i)
    (hycard : ∀ i, (y i).card = min (J i) (x i).card) :
    l1 (empHist y) (empHist x) = ∑ a, |(1 / (n : ℝ)) * ∑ i, (ind (x i) a - ind (y i) a)| ∧
    ∑ a, |(1 / (n : ℝ)) * ∑ i, (ind (x i) a - ind (y i) a)| =
      (1 / (n : ℝ)) * ∑ i, l1 (ind (x i)) (ind (y i)) ∧
    (1 / (n : ℝ)) * ∑ i, l1 (ind (x i)) (ind (y i)) ≤ (1 / (n : ℝ)) * ∑ i, ((k : ℝ) - J i) ∧
    (1 / (n : ℝ)) * ∑ i, ((k : ℝ) - J i) = k - (1 / (n : ℝ)) * ∑ i, (J i : ℝ) ∧
    (threshold n k D ≤ ∑ i, (J i : ℤ) → l1 (empHist y) (empHist x) ≤ D) := by sorry

end SparseHistComm
