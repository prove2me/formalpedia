-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_Supplement_ael_dimension_recovery
-- name    : SubspaceEvasion312.Explicit.Supplement.ael_dimension_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:49:27.841212+00:00
-- url     : https://prove2.me/theorems/6f31c7d7-cfb5-4211-80ac-fa8662554c45
-- title:
--   Theorem 32 — explicit additive codes that are (1−R−ε, ℓ, O(ℓ/ε)) dimension list-recoverable
-- statement:
--   There are absolute constants $K_1,K_2,h$ with the following property. For every finite field $\mathbb F_q$, every integer $\ell\ge1$ and every $\varepsilon\in(0,1)$ there is $K$ such that for every $R\in(0,1)$ there are an alphabet dimension $s$ with
--   $$1\le s\le q^{K_1\ell^2/\varepsilon^2}=\exp\!\big(K_1(\ell^2/\varepsilon^2)\ln q\big),$$
--   a threshold $m_0$, and for every block length $m\ge m_0$ an $\mathbb F_q$-additive code $C_m\subseteq(\mathbb F_q^s)^m$ with encoder $E_m$, such that
--
--   1. $\mathrm{rate}(C_m)\ge R$;
--   2. $C_m$ is $(1-R-\varepsilon,\ \ell,\ \lfloor K_2\ell/\varepsilon\rfloor)$ dimension list-recoverable;
--   3. the family is explicit: two fixed programs, given $m$, output a basis of $C_m$ (with its dimension) and $E_m(x)$ for every message $x$, each within charged time and word bound $K(m+1)^h$.
--
--   The low-dimensional list is what Theorem 28 needs: together with an evasive set it gives the nonlinear codes of Theorem 33.
--
--   **Formalization Note** $K$ depends on $q,\ell,\varepsilon$ but not on $R$, as in the published Theorem 17 on which the proof rests. When $R+\varepsilon>1$ the radius is negative and the recovered lists are empty. Time is measured in the mission's published register machine (field operations one step, program size charged).
--
--   Differences from the source:
--   - reading: s = exp(O(ℓ²/ε²) log q) → 1 ≤ s ≤ q^{K₁ℓ²/ε²} with absolute K₁ chosen before ℓ, ε, R, q; reason: uniform upper-bound reading of O; q^{x} = exp(x log q)
--   - reading: (1 − R − ε, ℓ, O(ℓ/ε)) dimension list-recoverable → dimension bound ⌊K₂ℓ/ε⌋ with absolute K₂ chosen first; reason: the proof gives 2ℓ/ε; ℓ/ε > 1 so no tail condition is needed
--   - reading: there exist explicit F_q-additive codes → for all block lengths m ≥ m₀, codes with encoders whose basis and encoding programs run in time K(m+1)^h, h absolute, K depending on q, ℓ, ε only; reason: explicit means polynomial-time constructible; the published Theorem 17 supplies this form
--   - encoding: lies in an r-dimensional subspace (Definition 27) → lies in a subspace of dimension at most r; reason: a subspace of dimension at most r lies in one of dimension exactly r when r ≤ sm
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, Explicit Subspace Evasive Sets via Subspace Designs, STOC 2027 submission #312 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf, PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc, Theorem 32, printed p. 15 (PDF p. 16); proof from [GGH26, Theorem 1.1] (Theorem 17) and [GG25, Lemma 2.10]

import Definitions.Def_SubspaceEvasion312_Explicit_Supplement_codes

namespace SubspaceEvasion312.Explicit.Supplement
/-- Theorem 32, printed p.15 (PDF p.16). Absolute K1, K2, h precede all parameters:
s <= q^(K1 l^2/eps^2) and the list lies in dimension <= K2 l/eps. The code family
is explicit: basis generation and encoding are fixed programs with time
K (m+1)^h for all large block lengths m, K depending on q, l, eps but not on R. -/
theorem ael_dimension_recovery :
    ∃ K₁ K₂ h : ℕ, 0 < K₁ ∧ 0 < K₂ ∧
    ∀ (F : Type) [Field F] [Fintype F] (ℓ : ℕ) (ε : ℝ), 1 ≤ ℓ → 0 < ε → ε < 1 →
    ∃ K : ℕ, 0 < K ∧
    ∀ R : ℝ, 0 < R → R < 1 →
    ∃ (s m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
      (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m) (gen enc : Program F),
      0 < s ∧ 0 < m₀ ∧
      (s : ℝ) ≤ (Fintype.card F : ℝ) ^ ((K₁ : ℝ) * (ℓ : ℝ) ^ 2 / ε ^ 2) ∧
      CodeAlgorithms k E gen enc (fun m => K * (m + 1) ^ h) (fun m => K * (m + 1) ^ h) m₀ ∧
      ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧ R ≤ codeRate (C m) ∧
        DimensionListRecoverable (C m) (1 - R - ε) ℓ ⌊(K₂ : ℝ) * ℓ / ε⌋₊ := by sorry
end SubspaceEvasion312.Explicit.Supplement
