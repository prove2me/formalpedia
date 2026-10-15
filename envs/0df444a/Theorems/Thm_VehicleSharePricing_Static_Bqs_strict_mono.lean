-- Prove2me | Theorems.Thm_VehicleSharePricing_Static_Bqs_strict_mono
-- name    : VehicleSharePricing.Static.Bqs_strict_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:24.361914+00:00
-- url     : https://prove2.me/theorems/9ae61715-664d-48f4-abc5-7a8a5dd9b5a7
-- title:
--   Proof of Theorem 2, p. 10 — $B^K_{i+1}(q^s)>B^K_i(q^s)$ for $i=1,\dots,K-1$
-- statement:
--   Let $q$ be a quantile policy that induces a strongly connected network, with workload $\lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}/\mu_{ij}$, and let $B^K_i(q)$ be the bound sequence of Theorem 2 with $\rho=\lambda/\mu$. Then for every $K$ and every $i=1,2,\dots,K-1$,
--   $$B^K_{i+1}(q)>B^K_i(q).$$
--
--   The bounds of Theorem 2 built from the policy's own workload thus improve strictly with each further iteration of the recursion.
--
--   **Formalization Note** Strictness needs $\lambda/\mu>0$, which follows from the hypotheses: the induced network has a pair with $\Lambda_{ij}q_{ij}>0$, and $\mu_{ij}>0$ there. Balanced flows are not needed and not assumed.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 10, proof of Theorem 2 ("using the same argument, we can get B^K_{i+1}(q^s) > B^K_i(q^s)")

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_Model
import Definitions.Def_VehicleSharePricing_Static_BoundSeq

namespace VehicleSharePricing.Static

/-- Proof of Theorem 2, p. 10: `B^K_{i+1}(q^s) > B^K_i(q^s)` for all `i = 1, …, K − 1`. For a
quantile policy `q` that induces a strongly connected network, with `λ/μ` its workload, the
bound sequence with `ρ = λ/μ` is strictly increasing in `i` on `1 ≤ i ≤ K`. -/
theorem Bqs_strict_mono {L : Type*} [Fintype L] [Nonempty L]
    (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q)
    (hconn : InducesStronglyConnected P q) (K i : ℕ) (hi : 1 ≤ i) (hiK : i + 1 ≤ K) :
    Bseq (Fintype.card L) (workload P q) K i <
      Bseq (Fintype.card L) (workload P q) K (i + 1) := by sorry

end VehicleSharePricing.Static
