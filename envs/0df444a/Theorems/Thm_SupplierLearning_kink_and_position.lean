-- Prove2me | Theorems.Thm_SupplierLearning_kink_and_position
-- name    : SupplierLearning.kink_and_position
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:25.682759+00:00
-- url     : https://prove2.me/theorems/d69704cf-1c48-40f9-9951-ef672c25aa3c
-- title:
--   Eqs. (21), (D), Cases 1–3 — the kink of $F$ and the position of the optimum (corrected: thresholds replaced by one-sided slopes)
-- statement:
--   Assume the second-order conditions, and write $k=\Delta c_1/r^h$, $y_k,z_k$ for the selected quantities at $k$. Then $F$ has right derivative $G(k,y_k)$ and left derivative $G(k,y_k)+g(y_k,z_k)$ at $k$, with $g(y_k,z_k)\ge0$, and $g(y_k,z_k)>0$ when $y_k>z_k$.
--
--   Moreover, if $(q,y,z)$ is a candidate, then $q$ is the unique maximizer of $F$ on $[0,Q]$, and:
--
--   1. (Case 1) if $G(k,y_k)>0$ then $q>k$;
--   2. (Case 2) if $G(k,y_k)+g(y_k,z_k)<0$ then $q<k$;
--   3. (Case 3) if $G(k,y_k)\le0\le G(k,y_k)+g(y_k,z_k)$ then $q=k$.
--
--   Differences from the source:
--   - reading: ν and ρ are priors, with no stated range → 0 < ν < 1 and 0 < ρ < 1 in Params.Standing; reason: the paper divides by 1 − ν, and the problem degenerates at the endpoints
--   - generalization: market sizes a_t and unit costs c^θ, implicitly positive → any real a_t and c^θ with c^ℓ < c^h; reason: no sign is used; positive values are a special case
--   - encoding: E_θ, E_Λ, a Bernoulli outcome Λ ∈ {0,1}, and types θ ∈ {ℓ,h} → two-term weighted sums, Λ as a Bool, θ as SupplierType; reason: Lean convention; same instances
--   - encoding: (C) q₁ ≤ Q with Q possibly ∞ → (r^h − r^ℓ) q₁ ≤ c^h − c^ℓ; reason: the same set for q₁ ≥ 0, and no ∞ is needed
--   - correction: (D) with strict inequality, and Cases 1–3 by the thresholds a̲, ā → g ≥ 0, strict when y_k > z_k; the cases by the signs of the one-sided slopes; reason: g = 0 when pooled at the kink; ā carries a spurious term: on the Table 5 base the correct threshold is 89.81, the printed one 97.01, and a₁ = 90 already has the optimum above the kink
--   - correction: the optimum is characterized under (A3) alone → hypothesis SecondOrder and an interior candidate; reason: (A3) does not bound the pooled case r^h ≤ ν r^ℓ, and corner optima are excluded by correction C3
--   - encoding: ∂F/∂q₁^h with one-sided evaluation → HasDerivWithinAt on Set.Ici and Set.Iic, with G and g explicit; reason: the two-sided derivative does not exist at the kink
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, (21), (D), Cases 1–3, App. p.8

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_Standing
import Definitions.Def_SupplierLearning_Params_slopeRight
import Definitions.Def_SupplierLearning_Params_slopeGap
import Definitions.Def_SupplierLearning_Params_Candidate
import Definitions.Def_SupplierLearning_Params_SecondOrder
import Definitions.Def_SupplierLearning_Params_periodTwoHigh
import Definitions.Def_SupplierLearning_Params_periodTwoLow
import Definitions.Def_SupplierLearning_Params_reducedValue
import Definitions.Def_SupplierLearning_Params_kinkPoint
import Definitions.Def_SupplierLearning_Params_capacityDomain

namespace SupplierLearning

/-- **Eqs. (21), (D), Cases 1–3 — the kink of F and the position of the optimum (corrected: thresholds replaced by one-sided slopes).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, (21), (D), Cases 1–3, App. p.8 (PDF p.40).

**Formalization Note.** The paper's thresholds `a̲, ā` are not stated: `ā` carries a spurious term, and they assume separation at the kink. The three cases are stated by the one-sided slopes themselves, which is what the thresholds encode. -/
theorem kink_and_position (P : Params) (hP : P.Standing) (hSO : P.SecondOrder) :
    let k := P.kinkPoint
    let yk := P.periodTwoHigh k
    let zk := P.periodTwoLow k
    HasDerivWithinAt P.reducedValue (P.slopeRight k yk) (Set.Ici k) k ∧
    HasDerivWithinAt P.reducedValue (P.slopeRight k yk + P.slopeGap yk zk) (Set.Iic k) k ∧
    0 ≤ P.slopeGap yk zk ∧
    (zk < yk → 0 < P.slopeGap yk zk) ∧
    ∀ q y z, P.Candidate q y z →
      (∀ q' ∈ P.capacityDomain, P.reducedValue q' ≤ P.reducedValue q ∧
        (P.reducedValue q' = P.reducedValue q → q' = q)) ∧
      (0 < P.slopeRight k yk → k < q) ∧
      (P.slopeRight k yk + P.slopeGap yk zk < 0 → q < k) ∧
      (P.slopeRight k yk ≤ 0 ∧ 0 ≤ P.slopeRight k yk + P.slopeGap yk zk → q = k) := by sorry

end SupplierLearning
