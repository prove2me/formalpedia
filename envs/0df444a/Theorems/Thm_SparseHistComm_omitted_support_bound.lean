-- Prove2me | Theorems.Thm_SparseHistComm_omitted_support_bound
-- name    : SparseHistComm.omitted_support_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:26.577303+00:00
-- url     : https://prove2.me/theorems/a6aea55c-bb79-4366-bfdd-94409218a927
-- title:
--   Proof of Lemma 2 — omitted-support bound and event inclusion (corrected: ≥ for the printed =)
-- statement:
--   Let $n \ge 1$, $1 \le k \le d$, $d \ge 2$, $0 \le D < k$. Let $X_1,\dots,X_n \subseteq \{1,\dots,d\}$ each have exactly $k$ elements, with empirical histogram $u$; let $I_1,\dots,I_n \subseteq \{1,\dots,d\}$ be arbitrary sets, $J_i = |X_i \cap I_i|$, and let $\hat u \in \mathbb R^d$ satisfy $\hat u \ge 0$. Then
--   $$
--   \|u - \hat u\|_1 \ \ge\ \frac{nk - \sum_i J_i}{n} - \sum_{i=1}^n \sum_{a=1}^d \hat u(a)\, \mathbf 1\{X_i(a) = 1,\ a \notin I_i\},
--   $$
--   and consequently, if $\sum_i J_i < nk - \lfloor nD\rfloor$ and $\|u - \hat u\|_1 \le D$, then
--   $$
--   \sum_{i=1}^n \sum_{a=1}^d \hat u(a)\, \mathbf 1\{X_i(a) = 1,\ a \notin I_i\} \ \ge\ \frac{\lfloor nD\rfloor + 1 - nD}{n}.
--   $$
--   If too few active coordinates are identified by the lists, an accurate estimate must put mass at least $(\lfloor nD\rfloor + 1 - nD)/n$ on active coordinates outside the lists. This is the event inclusion behind (17).
--
--   Differences from the source:
--   - correction: "Summing the coordinatewise lower bounds gives ∥u −û∥₁ = (nk − ∑ᵢJᵢ)/n − ∑ᵢ∑ₐ û(a)1{…}" (p.14) → ≥ in place of =; reason: summing lower bounds gives ≥, and = is false: n = 2, k = 1, d = 2, X₁ = X₂ = {a}, I₁ = I₂ = ∅, û = u gives left side 0 and right side 2/2 − 2 = −1; the p.15 display uses ≥
--   - generalization: Iᵢ the posterior lists of (16) and û the normalized decoder output → arbitrary sets Iᵢ ⊆ [d] and any û ≥ 0; reason: the argument is deterministic in (X, I, û) and uses only û ≥ 0, so the page's case is an instance
--   - encoding: binary vectors Xᵢ with exactly k active coordinates → supports Xᵢ : Finset (Fin d) with card = k; reason: bijection
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A (proof of Lemma 2), pp.14–15

import Mathlib
import Definitions.Def_SparseHistComm_empHist
import Definitions.Def_SparseHistComm_l1
import Definitions.Def_SparseHistComm_threshold

namespace SparseHistComm

/-- **Proof of Lemma 2, omitted-support bound and event inclusion** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A, pp.14–15),
with `≥` for the `=` printed on p.14. Let every `Xᵢ` have exactly `k` active coordinates, let
`Iᵢ ⊆ [d]` be any sets, `Jᵢ = |supp(Xᵢ) ∩ Iᵢ|`, `û ≥ 0` and `u` the empirical histogram of `X`.
Then `‖u − û‖₁ ≥ (nk − ∑ᵢ Jᵢ)/n − ∑ᵢ ∑ₐ û(a) 1{Xᵢ(a) = 1, a ∉ Iᵢ}`; hence on the event
`∑ᵢ Jᵢ < nk − ⌊nD⌋`, `‖u − û‖₁ ≤ D`,
`∑ᵢ ∑ₐ û(a) 1{Xᵢ(a) = 1, a ∉ Iᵢ} ≥ (⌊nD⌋ + 1 − nD)/n`.

**Formalization Note** Correction: the p.14 display reads "∥u −ˆu∥1 = …" after "Summing the
coordinatewise lower bounds gives"; summing lower bounds gives `≥`, and `=` is false
(`n = 2, k = 1, d = 2, X₁ = X₂ = {a}, I₁ = I₂ = ∅, û = u`: left `0`, right `2/2 − 2 = −1`). The
p.15 display uses `≥`. -/
theorem omitted_support_bound (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (D : ℝ) (hD0 : 0 ≤ D) (hDk : D < k)
    (X : Fin n → Finset (Fin d)) (hX : ∀ i, (X i).card = k) (I : Fin n → Finset (Fin d))
    (uhat : Fin d → ℝ) (huhat : ∀ a, 0 ≤ uhat a) :
    ((n : ℝ) * k - ∑ i, ((X i ∩ I i).card : ℝ)) / n
        - ∑ i, ∑ a, uhat a * (if a ∈ X i ∧ a ∉ I i then 1 else 0) ≤ l1 (empHist X) uhat ∧
    (∑ i, ((X i ∩ I i).card : ℤ) < threshold n k D → l1 (empHist X) uhat ≤ D →
      ((⌊(n : ℝ) * D⌋ : ℝ) + 1 - n * D) / n ≤
        ∑ i, ∑ a, uhat a * (if a ∈ X i ∧ a ∉ I i then 1 else 0)) := by sorry

end SparseHistComm
