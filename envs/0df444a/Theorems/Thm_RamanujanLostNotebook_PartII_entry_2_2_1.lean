-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartII_entry_2_2_1
-- name    : RamanujanLostNotebook.PartII.entry_2_2_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:29:50.270389+00:00
-- url     : https://prove2.me/theorems/a0b05383-4bf2-453a-b96b-bfd471d489ce
-- title:
--   A two-series Sears transformation
-- statement:
--   Let a,q be complex with |q|<1 and 0<|aq|<1. For each n≥0 the product (q^{2n+3}/a;q²)_∞ converges. The sums S=∑_{n≥0}(-q;q)_{2n}q^n(q^{2n+3}/a;q²)_∞/(aq;q²)_{n+1} and T=∑_{n≥0}(-q/a;q)_{2n}a^nq^n(q^{2n+3}/a;q²)_∞/(q;q²)_{n+1} converge absolutely and S=T. Differs from the printed source: we make |q|<1 explicit and multiply both printed sides by (q/a;q²)_∞, so that (q/a;q²)_{n+1} in the denominators becomes the tail (q^{2n+3}/a;q²)_∞. This is our interpretation: it covers every a with 0<|aq|<1, including the points a=q^{2k+1} where the printed denominator (q/a;q²)_{n+1} vanishes for n≥k, and on the regular locus it is the printed identity times the nonzero (q/a;q²)_∞. The pre-compile audit evaluated the cleared sums at q=a=1/2 (common value 3.78970506653066247820254749844), at q=0.6, a=q³ (4.12427408786199190030650428409) and at a complex pole, with residuals at most 3.3e−61; an independent 60-digit check in this revision agrees. Numerical evidence, not a proof, supports the continuation in a.
--
--   **Discrepancy from the printed source.** Differs from the printed source: we make |q|<1 explicit and multiply both printed sides by (q/a;q²)_∞, so that (q/a;q²)_{n+1} in the denominators becomes the tail (q^{2n+3}/a;q²)_∞. This is our interpretation: it covers every a with 0<|aq|<1, including the points a=q^{2k+1} where the printed denominator (q/a;q²)_{n+1} vanishes for n≥k, and on the regular locus it is the printed identity times the nonzero (q/a;q²)_∞. The pre-compile audit evaluated the cleared sums at q=a=1/2 (common value 3.78970506653066247820254749844), at q=0.6, a=q³ (4.12427408786199190030650428409) and at a complex pole, with residuals at most 3.3e−61; an independent 60-digit check in this revision agrees. Numerical evidence, not a proof, supports the continuation in a.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 2, Entry 2.2.1, p. 45.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf

namespace RamanujanLostNotebook.PartII
theorem entry_2_2_1 (a q : ℂ) (hq : ‖q‖ < 1)
    (haq0 : 0 < ‖a * q‖) (haq : ‖a * q‖ < 1) :
    (∀ n : ℕ, Multipliable (fun k : ℕ =>
      1 - ((q / a) * (q ^ 2) ^ (n + 1)) * (q ^ 2) ^ k)) ∧
    ∃ s : ℂ,
      HasSum (fun n : ℕ => qPoch (-q) q (2 * n) * q ^ n *
        qPochInf ((q / a) * (q ^ 2) ^ (n + 1)) (q ^ 2) /
        qPoch (a * q) (q ^ 2) (n + 1)) s ∧
      HasSum (fun n : ℕ => qPoch (-q / a) q (2 * n) * a ^ n * q ^ n *
        qPochInf ((q / a) * (q ^ 2) ^ (n + 1)) (q ^ 2) /
        qPoch q (q ^ 2) (n + 1)) s := by sorry
end RamanujanLostNotebook.PartII
