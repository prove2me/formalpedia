-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_quadratic_code_family
-- name    : SubspaceEvasion312.Explicit.quadratic_code_family
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:11.040582+00:00
-- url     : https://prove2.me/theorems/9d31a951-280a-4d77-89a1-3c9f1622dc2e
-- title:
--   Corollary 18 — the quadratic-branch code family
-- statement:
--   There are absolute $A>0,a,h$. For every finite field $F_q$ and positive integer $r$, there are positive $s,K,m_0$ and a family of additive codes $C_m\le(F_q^s)^m$, for every $m\ge m_0$, with
--
--   $$s\le A(1+r)^a q^{r^2},\qquad\operatorname{rate}(C_m)\ge\frac1{2r},\qquad\tau_m(r)<\frac1r.$$
--
--   Each code is a $\tau_m$-subspace design and is $(r,0,\ell,\ell)$ subspace list-recoverable for every independent $\ell\in\mathbb N$. Uniform basis-generation and dimension-correct encoding programs run in time $K(m+1)^h$, with all setup charged and polynomially bounded natural registers. This supplies the entire Case A code family, including its alphabet dimension and effectiveness.
--
--   Differences from the source:
--   - encoding: finite-field vectors and additive codes → functions on Fin and Mathlib submodules over an arbitrary finite field; reason: these are exactly the source vector spaces and F-linear codes; dimension is over the base field
--   - encoding: explicit code computable in fixed-parameter polynomial time → uniform finite field-register programs generating a basis and evaluating a dimension-correct encoder, with program loading and all transitions charged; reason: makes the computational conclusion operational; natural registers have polynomial value bounds, so their word lengths are logarithmic in block length; constants and polynomial degrees are quantified
--   - encoding: r∈N in the expressions 1/(2r) and 1/r → r>0; reason: these are the source reciprocal formulas on their meaningful domain; the undefined r=0 rate is not replaced by Lean division by zero
--   - encoding: s=poly(r) q^(r²) → an absolute polynomial bound with all constants and degrees quantified first; reason: retains the full stated parameter dependence
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Corollary 18, printed p. 10 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc

import Definitions.Def_SubspaceEvasion312_Explicit_effective

namespace SubspaceEvasion312.Explicit
open scoped ENNReal
/-- Corollary 18, printed p.10 (PDF p.11). -/
theorem quadratic_code_family :
    ∃ A a h : ℕ, 0 < A ∧
    ∀ (F : Type) [Field F] [Fintype F] (r : ℕ), 0 < r →
    ∃ (s K m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
      (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m)
      (τ : ℕ → ℕ → ℝ) (gen enc : Program F),
      0 < s ∧ 0 < K ∧ 0 < m₀ ∧
      (s : ℝ) ≤ A * (1 + (r : ℝ))^a * (Fintype.card F : ℝ)^(r^2) ∧
      CodeAlgorithms k E gen enc (fun m => K*(m+1)^h) (fun m => K*(m+1)^h) m₀ ∧
      ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧ 1 / (2*(r : ℝ)) ≤ codeRate (C m) ∧
        SubspaceDesign (C m) (τ m) ∧ τ m r < 1 / (r : ℝ) ∧
        ∀ ℓ : ℕ, ListRecoverable (C m) r 0 ℓ ℓ := by sorry
end SubspaceEvasion312.Explicit
