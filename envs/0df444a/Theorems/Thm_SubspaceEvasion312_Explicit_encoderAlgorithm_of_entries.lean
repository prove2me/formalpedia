-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_encoderAlgorithm_of_entries
-- name    : SubspaceEvasion312.Explicit.encoderAlgorithm_of_entries
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:23:14.409805+00:00
-- url     : https://prove2.me/theorems/c3e684f4-6371-4f64-b5ad-035418790c46
-- title:
--   Uniform generator-matrix entries compile to matrix–vector encoding
-- statement:
--   A uniform generator-matrix oracle yields one fixed matrix–vector multiplication program for the whole encoder family.
--
--   Let $E_m:F^{k_m}\to(F^s)^m$ be $F$-linear, with $k_m\le sm$ eventually. Suppose fixed programs compute $k_m$ and every entry $E_m(e_j)_{i,u}$ from $(m,j,i,u)$, within time and natural-register bound $K_0(m+1)^{h_0}$. There is an absolute exponent $c$, a fixed program, and a threshold $m_1\ge m_0$ such that for every $m\ge m_1$ and every $x\in F^{k_m}$ the program outputs
--   \[
--   \bigl(E_m(x)_{i,u}\bigr)_{i<m,\;u<s}
--   =\left(\sum_{j<k_m}x_jE_m(e_j)_{i,u}\right)_{i<m,\;u<s}
--   \]
--   in block-serial order, within time and register bound $K_0(s+2)^c(m+1)^{h_0+c}$.
--
--   This is the matrix–vector evaluation half of the generic compiler used to make the explicit-code conclusion of Theorem 17 operational.
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 17 and its explicit linear-code convention, printed p.10 (PDF p.11); machine conventions and Theorem 8 proof, printed pp.7–8 (PDF pp.8–9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf. This lemma isolates the matrix–vector multiplication loop of the generic generator-matrix implementation.

import Definitions.Def_SubspaceEvasion312_Explicit_effective

namespace SubspaceEvasion312.Explicit

/-- A uniform generator-matrix presentation compiles to matrix–vector encoding. -/
theorem encoderAlgorithm_of_entries :
    ∃ c : ℕ, ∀ (F : Type) [Field F] (s h₀ K₀ m₀ : ℕ)
      (k : ℕ → ℕ) (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m)
      (dim entry : Program F), 0 < K₀ →
      (∀ m ≥ m₀, k m ≤ s * m) →
      (∀ m ≥ m₀,
        RunsWithin dim [m] [] (K₀ * (m+1)^h₀) (K₀ * (m+1)^h₀) [] [k m] ∧
        ∀ (j : Fin (k m)) (i : Fin m) (u : Fin s),
          RunsWithin entry [m, j.val, i.val, u.val] []
            (K₀ * (m+1)^h₀) (K₀ * (m+1)^h₀)
            [E m (Pi.single j 1) i u]) →
      ∃ (enc : Program F) (m₁ : ℕ), m₀ ≤ m₁ ∧
        ∀ m ≥ m₁, ∀ x, RunsWithin enc [m] (vectorData x)
          (K₀ * (s+2)^c * (m+1)^(h₀+c))
          (K₀ * (s+2)^c * (m+1)^(h₀+c))
          (blockData (E m x)) := by sorry
