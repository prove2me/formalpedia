-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartII_equation_5_2_3
-- name    : RamanujanLostNotebook.PartII.equation_5_2_3
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T04:50:48.962002+00:00
-- url     : https://prove2.me/theorems/b652a2bf-0264-46ee-b1ae-810316294299
-- title:
--   Even-centered Bailey theta transform
-- statement:
--   Write (x;b)_n=∏_{k=0}^{n−1}(1−x b^k), (x;b)_∞=∏_{k≥0}(1−x b^k), f(u,v)=∑_{j∈ℤ}u^(j(j+1)/2)v^(j(j−1)/2), ψ(z)=∑_{n≥0}z^(n(n+1)/2), and E(z)=(z;z)_∞. For base B, D(q,B) consists of complex pairs (r,s) with r,s≠0, |q²/(rs)|<1, and (q²/r)B^k≠1, (q²/s)B^k≠1 for all integers k≥0. Let U_n=(r;q²)_n(s;q²)_n(−aq;q²)_n(−q/a;q²)_n(q²/(rs))^n/(q²;q²)_(2n). For complex |q|<1, a≠0 and (r,s)∈D(q,q²), ∑_{n≥0}U_n converges absolutely to [(q²/r;q²)_∞(q²/s;q²)_∞/((q²;q²)_∞(q²/(rs);q²)_∞)]·[1+∑_{N≥1}(r;q²)_N(s;q²)_N(a^N+a^(−N))q^(N²+2N)/((rs)^N(q²/r;q²)_N(q²/s;q²)_N)]. The N≥1 row is also absolutely summable. Differs from the printed source: we spell out the ordinary convergence range |q²/(rho₁ rho₂)|<1 and exclude reciprocal-product poles; pp.98–99 leave these parameter restrictions implicit. These domain conditions are ours, not an assumed identity.
--
--   **Discrepancy from the printed source.** Differs from the printed source: we spell out the ordinary convergence range |q²/(rho₁ rho₂)|<1 and exclude reciprocal-product poles; pp.98–99 leave these parameter restrictions implicit. These domain conditions are ours, not an assumed identity.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 5, Equation 5.2.3, p. 98, eq. (5.2.3).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch05_ch05EvenTerm
import Definitions.Def_RamanujanLostNotebook_PartII_ch05_ch05ParameterDomain
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf

namespace RamanujanLostNotebook.PartII
theorem equation_5_2_3 (q a rho₁ rho₂ : ℂ) (hq : ‖q‖ < 1) (ha : a ≠ 0)
    (hrho : (rho₁, rho₂) ∈ ch05ParameterDomain q (q ^ 2)) :
    HasSum (fun n : ℕ => ch05EvenTerm q a rho₁ rho₂ n)
      (qPochInf (q ^ 2 / rho₁) (q ^ 2) * qPochInf (q ^ 2 / rho₂) (q ^ 2) /
        (qPochInf (q ^ 2) (q ^ 2) * qPochInf (q ^ 2 / (rho₁ * rho₂)) (q ^ 2)) *
        (1 + ∑' k : ℕ,
          qPoch rho₁ (q ^ 2) (k + 1) * qPoch rho₂ (q ^ 2) (k + 1) *
            (a ^ (k + 1) + (a⁻¹) ^ (k + 1)) * q ^ ((k + 1) ^ 2 + 2 * (k + 1)) /
            ((rho₁ * rho₂) ^ (k + 1) * qPoch (q ^ 2 / rho₁) (q ^ 2) (k + 1) *
              qPoch (q ^ 2 / rho₂) (q ^ 2) (k + 1)))) ∧
    Summable (fun k : ℕ => qPoch rho₁ (q ^ 2) (k + 1) * qPoch rho₂ (q ^ 2) (k + 1) *
        (a ^ (k + 1) + (a⁻¹) ^ (k + 1)) * q ^ ((k + 1) ^ 2 + 2 * (k + 1)) /
        ((rho₁ * rho₂) ^ (k + 1) * qPoch (q ^ 2 / rho₁) (q ^ 2) (k + 1) *
          qPoch (q ^ 2 / rho₂) (q ^ 2) (k + 1))) := by sorry
end RamanujanLostNotebook.PartII
