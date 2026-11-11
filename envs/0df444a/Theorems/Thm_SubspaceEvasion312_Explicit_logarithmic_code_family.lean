-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_logarithmic_code_family
-- name    : SubspaceEvasion312.Explicit.logarithmic_code_family
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:18.060127+00:00
-- url     : https://prove2.me/theorems/b331fee4-978f-4978-9079-4e50829f5ec0
-- title:
--   Corollary 19 — the logarithmic-branch code family
-- statement:
--   There are absolute $A>0,a,h$. For every finite field $F_q$, $r\in\mathbb N$ and prescribed positive input-list size $\ell$, there exist positive $s,K,m_0$ and codes $C_m\le(F_q^s)^m$ for every $m\ge m_0$, with
--
--   $$s\le A(1+r+\log_2\ell)^a q^{r^2},\quad\operatorname{rate}(C_m)\ge\frac1{2+2\log_2\ell},\quad\tau_m(r)\le\frac1{1+\log_2\ell}.$$
--
--   They are $\tau_m$-subspace designs and $(r,0,\ell,2\ell)$ subspace list-recoverable. Their basis-generation and dimension-correct encoding programs have time and natural-register bounds $K(m+1)^h$, including setup. The multiplier and threshold may depend on the prescribed $\ell$ as well as $q,r$. No independent universal list-size variable is asserted for the same code. This supplies every clause of the Case B family, including $r=0$ and $\ell=1$.
--
--   Differences from the source:
--   - encoding: finite-field vectors and additive codes → functions on Fin and Mathlib submodules over an arbitrary finite field; reason: these are exactly the source vector spaces and F-linear codes; dimension is over the base field
--   - encoding: explicit code computable in fixed-parameter polynomial time → uniform finite field-register programs generating a basis and evaluating a dimension-correct encoder, with program loading and all transitions charged; reason: makes the computational conclusion operational; natural registers have polynomial value bounds, so their word lengths are logarithmic in block length; constants and polynomial degrees are quantified
--   - reading: O_{q,r}(1) alongside a displayed alphabet formula depending on ℓ and a repeated concluding ℓ → ℓ is prescribed for the family, with multiplier and threshold allowed to depend on q,r,ℓ; reason: the displayed polynomial in log ℓ already requires fixing ℓ; the last ℓ is the same parameter, not an independent guarantee for every list size
--   - encoding: r,ℓ∈N and logarithmic reciprocal formulas → all r∈N and positive ℓ, with an absolute polynomial alphabet bound; reason: the logarithm requires positive ℓ; no restriction on positive ℓ or field characteristic is added
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Corollary 19, printed p. 11 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc

import Definitions.Def_SubspaceEvasion312_Explicit_effective

namespace SubspaceEvasion312.Explicit
open scoped ENNReal
/-- Corollary 19, printed p.11 (PDF p.12). The prescribed ell is fixed for
the family; the runtime factor may depend on ell. -/
theorem logarithmic_code_family :
    ∃ A a h : ℕ, 0 < A ∧
    ∀ (F : Type) [Field F] [Fintype F] (r ℓ : ℕ), 0 < ℓ →
    ∃ (s K m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
      (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m)
      (τ : ℕ → ℕ → ℝ) (gen enc : Program F),
      0 < s ∧ 0 < K ∧ 0 < m₀ ∧
      (s : ℝ) ≤ A * (1 + r + log₂ (ℓ : ℝ))^a * (Fintype.card F : ℝ)^(r^2) ∧
      CodeAlgorithms k E gen enc (fun m => K*(m+1)^h) (fun m => K*(m+1)^h) m₀ ∧
      ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧
        1 / (2 + 2 * log₂ (ℓ : ℝ)) ≤ codeRate (C m) ∧
        SubspaceDesign (C m) (τ m) ∧ τ m r ≤ 1 / (1 + log₂ (ℓ : ℝ)) ∧
        ListRecoverable (C m) r 0 ℓ (2*ℓ) := by sorry
end SubspaceEvasion312.Explicit
