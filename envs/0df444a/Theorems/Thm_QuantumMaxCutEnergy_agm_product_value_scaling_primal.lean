-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_product_value_scaling_primal
-- name    : QuantumMaxCutEnergy.agm_product_value_scaling_primal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:26:24.206858+00:00
-- url     : https://prove2.me/theorems/c30dc1ae-6929-40ac-860c-e94fef87b521
-- title:
--   The AGM scaling from a primal point alone, with no duality gap
-- statement:
--   **The AGM comparison from a primal point alone — no duality gap required.**
--
--   Let $O$ be the quantum optimum, $W$ the total weight, $S$ the Max-Cut SDP optimum and $L\ge0$ a rational value with $L\le S$. Suppose only
--   $$L\;\ge\;\frac{0.953}{0.954}\cdot\frac{O+W}{3}.$$
--   Then
--   $$0\le 0.954\,L,\qquad 0.954\,L\le O,\qquad \frac{0.953\,(O+W)}{3}\le 0.954\,L .$$
--
--   The third inequality is exact: multiplying by $0.954$ turns $\frac{0.953}{0.954}\cdot\frac{O+W}{3}$ into $\frac{0.953(O+W)}{3}$, since $0.954\cdot\frac{0.953}{0.954}=0.953$; no approximation is involved. The second follows from $L\le S$ and the rank-three gap $0.954\,S\le O$.
--
--   The point is what is **absent**: the already-proved `agm_product_value_scaling` requires the duality gap $S-L\le W/10^4$, which forces $L$ to track the *optimal* value and hence to come with a near-optimal dual certificate. Here that hypothesis is replaced by a fixed lower bound on $L$ alone. Any $L$ satisfying the old hypotheses satisfies the new one, because $S\ge (O+W)/3$ and $W/10^4$ is far smaller than the $0.105\%$ slack between the constants $0.953$ and $0.954$. So this is a strict weakening of the hypothesis: a primal feasible point suffices, and the dual solution is off the critical path.
--
--   Note also that $S$ enters only through $L\le S$; the structural domination $(O+W)/3\le S$ is not needed for the inequalities themselves.
-- source:
--   AGM / Anshu-Gosset-Morenz rounding comparison, with the duality-gap hypothesis replaced by a primal lower bound; QuantumMaxCutEnergy.agm_product_value_scaling obtained from this work.

import Mathlib

open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **The AGM value scaling from a primal point alone.** -/
theorem agm_product_value_scaling_primal (O W S L : ℝ)
    (hstruct : (O + W) / 3 ≤ S)
    (hgap : (0.954 : ℝ) * S ≤ O)
    (hL0 : 0 ≤ L) (hLS : L ≤ S)
    (hLlow : (0.953 / 0.954) * ((O + W) / 3) ≤ L) :
    0 ≤ (0.954 : ℝ) * L ∧
      (0.954 : ℝ) * L ≤ O ∧
        (0.953 : ℝ) * (O + W) / 3 ≤ (0.954 : ℝ) * L := by sorry

end QuantumMaxCutEnergy
