-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_theorem_2
-- name    : VeinottSensitiveDP.Sensitive.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:21.643011+00:00
-- url     : https://prove2.me/theorems/cd30cb96-edd5-4e74-8bc1-edb700b6ed67
-- title:
--   Theorem 2 — if ρ ≠ 0 and |σ(ρH)| < 1, then ρ ∉ σ(Q) and R_ρ(Q) = ρ⁻¹P* + Σ (−ρ)ⁿHⁿ⁺¹
-- statement:
--   Let $P$ be an $S\times S$ substochastic matrix, $Q=P-I$, $P^*$ the Cesàro limit of the powers of $P$ and $H=(I-P+P^*)^{-1}-P^*$. If $\rho\neq0$ is real and $|\sigma(\rho H)|<1$, then $\rho\notin\sigma(Q)$, the series below converges, and
--   $$R_\rho(Q)=\rho^{-1}P^*+\sum_{n=0}^\infty(-\rho)^nH^{n+1}. \tag{26}$$
--
--   This is the Laurent expansion of the resolvent of $Q$ about $\rho=0$: a simple pole with residue $P^*$ plus a power series in the powers of the deviation matrix $H$.
--
--   **Formalization Note** $|\sigma(\cdot)|$ is the spectral radius of the complexified matrix; the series is a matrix `tsum`, and its convergence is part of the conclusion.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1643, §3, Theorem 2, (26)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- Theorem 2 (Laurent expansion of the resolvent): let `P` be an `S × S` substochastic matrix,
`Q = P − I`, `P* = limitMatrix P` and `H = H₀ = deviationMatrix P`. If `ρ ≠ 0` and
`|σ(ρH)| < 1`, then `ρ ε σ(Q)ᶜ`, the series `Σ_{n≥0} (−ρ)ⁿHⁿ⁺¹` converges, and
(26) `R_ρ(Q) = ρ⁻¹P* + Σ_{n=0}^∞ (−ρ)ⁿHⁿ⁺¹`.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1643, §3, Theorem 2, (26).

**Formalization Note.** `ρ` is real; `|σ(·)|` is the complexified spectral radius `specRad`;
`R_ρ(Q)` is `resolvent ρ (P − 1)`. Convergence of the series (entrywise) is stated, so the
`tsum` is the genuine sum. -/
theorem theorem_2 {St : Type} [Fintype St] [DecidableEq St] (P : Matrix St St ℝ)
    (hP : IsSubstochastic P) (ρ : ℝ) (hρ : ρ ≠ 0) (hH : VeinottSensitiveDP.Transient.specRad (ρ • deviationMatrix P) < 1) :
    ρ ∉ spectrum ℝ (P - 1) ∧
      Summable (fun n : ℕ => (-ρ) ^ n • deviationMatrix P ^ (n + 1)) ∧
      resolvent ρ (P - 1) =
        ρ⁻¹ • limitMatrix P + ∑' n : ℕ, (-ρ) ^ n • deviationMatrix P ^ (n + 1) := by sorry

end VeinottSensitiveDP.Sensitive
