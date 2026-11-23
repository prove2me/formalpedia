-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_generatorAlgorithm_of_entries
-- name    : SubspaceEvasion312.Explicit.generatorAlgorithm_of_entries
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:49.232966+00:00
-- url     : https://prove2.me/theorems/f8a7c981-218a-4183-8e35-5f54ed477187
-- title:
--   Uniform generator-matrix entries compile to basis generation
-- statement:
--   A uniform generator-matrix oracle yields one fixed program that serializes the basis of every encoder in the family.
--
--   Let $E_m:F^{k_m}\to(F^s)^m$ be $F$-linear, with $k_m\le sm$ eventually. Suppose fixed programs compute $k_m$ and every entry $E_m(e_j)_{i,u}$ from $(m,j,i,u)$, within time and natural-register bound $K_0(m+1)^{h_0}$. There is an absolute exponent $c$, a fixed program, and a threshold $m_1\ge m_0$ such that for every $m\ge m_1$ the program outputs the natural number $k_m$ and the list
--   \[
--   \bigl(E_m(e_j)_{i,u}\bigr)_{j<k_m,\;i<m,\;u<s}
--   \]
--   in lexicographic order, within time and register bound $K_0(s+2)^c(m+1)^{h_0+c}$.
--
--   This is the basis-generation half of the generic matrix–vector compiler used to make the explicit-code conclusion of Theorem 17 operational.
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 17 and its explicit linear-code convention, printed p.10 (PDF p.11); machine conventions and Theorem 8 proof, printed pp.7–8 (PDF pp.8–9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf. This lemma isolates the basis-serialization loop of the generic generator-matrix implementation.

import Definitions.Def_SubspaceEvasion312_Explicit_effective

namespace SubspaceEvasion312.Explicit

/-- A uniform generator-matrix presentation compiles to a basis-generation program. -/
theorem generatorAlgorithm_of_entries :
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
      ∃ (gen : Program F) (m₁ : ℕ), m₀ ≤ m₁ ∧
        ∀ m ≥ m₁, RunsWithin gen [m] []
          (K₀ * (s+2)^c * (m+1)^(h₀+c))
          (K₀ * (s+2)^c * (m+1)^(h₀+c))
          (basisData (E m)) [k m] := by sorry
