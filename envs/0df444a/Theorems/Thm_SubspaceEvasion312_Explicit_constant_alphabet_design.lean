-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_constant_alphabet_design
-- name    : SubspaceEvasion312.Explicit.constant_alphabet_design
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:27.640544+00:00
-- url     : https://prove2.me/theorems/6bfc5a26-4bab-4a2d-b480-ad3ba7987cda
-- title:
--   Theorem 17 — constant-alphabet subspace-design codes
-- statement:
--   There are absolute integers $A>0,a,h$ with the following property. For every finite field $F_q$, rank $r\in\mathbb N$ and real $\delta\in(0,1]$, there is a time multiplier $K=K(q,r,\delta)>0$. For every $R>0$ with $R+\delta\le1$, there is a positive block dimension $s$ and a threshold $m_0$, followed by additive codes $C_m\le(F_q^s)^m$ for every $m\ge m_0$, such that
--
--   $$s\le A(1+r+1/\delta)^a q^{r^2},\qquad\operatorname{rate}(C_m)\ge R,\qquad\tau_m(r)\le R+\delta.$$
--
--   Each $C_m$ is a $\tau_m$-subspace design. Fixed programs generate a basis and its dimension and evaluate a linear encoder with image $C_m$ and domain dimension $\dim C_m$, in time $K(m+1)^h$, including setup. Natural registers have the same polynomial value bound. This is the constant-field code family used by both branches of the evasion construction. The time multiplier is independent of $R$, as the source subscript specifies; the threshold may depend on $R$.
--
--   Differences from the source:
--   - encoding: finite-field vectors and additive codes → functions on Fin and Mathlib submodules over an arbitrary finite field; reason: these are exactly the source vector spaces and F-linear codes; dimension is over the base field
--   - encoding: explicit code computable in fixed-parameter polynomial time → uniform finite field-register programs generating a basis and evaluating a dimension-correct encoder, with program loading and all transitions charged; reason: makes the computational conclusion operational; natural registers have polynomial value bounds, so their word lengths are logarithmic in block length; constants and polynomial degrees are quantified
--   - encoding: s=poly(r,1/δ) q^(r²) → s≤A(1+r+1/δ)^a q^(r²), with A,a and the runtime degree before every field and parameter; reason: exposes the polynomial and its uniform constants; no dimension or field is fixed
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 17, printed p. 10 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc

import Definitions.Def_SubspaceEvasion312_Explicit_effective

namespace SubspaceEvasion312.Explicit
/-- Theorem 17, printed p.10 (PDF p.11). All polynomial degrees are absolute.
The time multiplier is uniform in R, as the displayed O_{q,r,epsilon} specifies. -/
theorem constant_alphabet_design :
    ∃ A a h : ℕ, 0 < A ∧
    ∀ (F : Type) [Field F] [Fintype F] (r : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ K : ℕ, 0 < K ∧
    ∀ R : ℝ, 0 < R → R + ε ≤ 1 →
    ∃ (s m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
      (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m)
      (τ : ℕ → ℕ → ℝ) (gen enc : Program F),
      0 < s ∧ 0 < m₀ ∧ (s : ℝ) ≤ A * (1 + r + 1 / ε)^a * (Fintype.card F : ℝ)^(r^2) ∧
      CodeAlgorithms k E gen enc (fun m => K * (m+1)^h) (fun m => K * (m+1)^h) m₀ ∧
      ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧ R ≤ codeRate (C m) ∧
        SubspaceDesign (C m) (τ m) ∧ τ m r ≤ R + ε := by sorry
end SubspaceEvasion312.Explicit
