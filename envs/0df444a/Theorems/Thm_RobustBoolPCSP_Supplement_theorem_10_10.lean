-- Prove2me | Theorems.Thm_RobustBoolPCSP_Supplement_theorem_10_10
-- name    : RobustBoolPCSP.Supplement.theorem_10_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:41:35.466522+00:00
-- url     : https://prove2.me/theorems/592223f5-ae23-4d44-aaeb-422bea7e2025
-- title:
--   Theorem 10.10 (Low-influence finite-product bound) — average modified-test rejection $\ge cv/\log^2(e/v)$
-- statement:
--   There is an absolute constant $c>0$ such that for every rational $0<v\le1/10$ there are an integer $D\ge1$ and a rational $\tau>0$ with the following property. For every word length $R$ and all fuzzy $F:\{-1,1\}^R\to\Delta(B)$, $G:(A,\nu_v)^R\to\Delta(B)$, if every color coordinate of $F$ and of $G$ has all degree-at-most-$D$ influences at most $\tau$, then the average rejection of the three modified tests of §10.4 is at least
--
--   $$\lambda(v)=\frac{cv}{\log^2(e/v)}.$$
--
--   $D$ and $\tau$ depend on $v$ but not on $R$.
--
--   Differences from the source:
--   - reading: A smaller positive rational lower bound for λ(v) may be used in the reduction. → not stated as a separate assertion; reason: a remark on how the bound is used; any smaller lower bound follows trivially
--   - encoding: binary words {−1,1}^R and A = {−1, 0, 1} → Fin R → Bool (true = 1) and Fin R → SignType; reason: same spaces
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), Theorem 10.10, p.89

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_FiniteTests

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

/-- **Theorem 10.10 (Low-influence finite-product bound)**, p.89. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"There is an absolute c > 0 such that, for every fixed rational 0 < v ≤ 1/10, there are an integer
D ≥ 1 and a positive rational τ with the following property. For every word length R, if all color
coordinates of F and G have all degree-at-most-D influences at most τ, their average modified-test
rejection is at least λ(v) = cv/log²(e/v). (109) The parameters D, τ depend on v, not on R. A smaller
positive rational lower bound for λ(v) may be used in the reduction." Setting (§10.4, p.89): fuzzy
functions `F : {−1,1}^R → ∆(B)`, `G : (A, ν_v)^R → ∆(B)`, the modified antipodal and erasure tests
and the equality test, each of weight 1/3, and the influences in the product bases (108).

**Formalization Note.** The average rejection is `avgModRej`; influences of the color coordinates
`F_b`, `G_b` are `infLeB`, `infLeT`. Quantifier order: `c`, then `v`, then `D, τ`, then `R`, `F`, `G`.
The last sentence of the theorem is a remark on the use of the bound and is not a separate
assertion. -/
theorem theorem_10_10 :
    ∃ c : ℝ, 0 < c ∧ ∀ v : ℚ, 0 < v → v ≤ 1 / 10 → ∃ (D : ℕ) (τ : ℚ), 1 ≤ D ∧ 0 < τ ∧
      ∀ (R : ℕ) (F : (Fin R → Bool) → ZMod 5 → ℝ) (G : (Fin R → SignType) → ZMod 5 → ℝ),
        IsFuzzyFin F → IsFuzzyFin G →
        (∀ (b : ZMod 5) (i : Fin R), infLeB D (fun x => F x b) i ≤ τ) →
        (∀ (b : ZMod 5) (i : Fin R), infLeT v D (fun x => G x b) i ≤ τ) →
          c * v / (Real.log (Real.exp 1 / v)) ^ 2 ≤ avgModRej v F G := by sorry

end RobustBoolPCSP.Supplement
