-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_codeAlgorithms_of_entries
-- name    : SubspaceEvasion312.Explicit.codeAlgorithms_of_entries
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:52:17.590864+00:00
-- url     : https://prove2.me/theorems/5d3c24d9-5996-4386-b984-1ccedeb84be2
-- title:
--   Uniform generator-matrix programs compile to basis and encoder programs
-- statement:
--   There is an absolute exponent $c$ such that every uniformly presented family of linear encoders can be evaluated on the same finite field-register machine used by Theorem 17.
--
--   Let $E_m:F^{k_m}\to(F^s)^m$ be $F$-linear, with $k_m\le sm$. Suppose one fixed program computes $k_m$ from $m$, and another fixed program computes the generator-matrix entry $E_m(e_j)_{i,u}$ from $(m,j,i,u)$. If both run in time and natural-register bound $K_0(m+1)^{h_0}$, then there are fixed programs generating the serialized basis of $E_m$ and evaluating $E_m(x)$ on every input, within time and register bound
--   \[
--   K_0(s+2)^c(m+1)^{h_0+c},
--   \]
--   starting at some threshold $m_1\ge m_0$.
--
--   The algorithm is the ordinary matrix–vector multiplication: triple loops over $j,i,u$ generate the basis, and for encoding one accumulates $E_m(x)_{i,u}=\sum_jx_jE_m(e_j)_{i,u}$. This separates generic program construction from the algebraic subspace-design theorem. The bound $k_m\le sm$ is essential for bounding all loop counters and runtime independently of the particular code.
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 17 and its explicit linear-code convention, printed p.10 (PDF p.11); complexity conventions and Theorem 8 proof, printed pp.7–8 (PDF pp.8–9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf. This lemma is the generic matrix–vector implementation used to make that explicit code conclusion operational.

import Definitions.Def_SubspaceEvasion312_Explicit_effective

/-- A uniform generator-matrix presentation compiles to basis generation and encoding. -/
theorem SubspaceEvasion312.Explicit.codeAlgorithms_of_entries :
    ∃ c : ℕ, ∀ (F : Type) [Field F] (s h₀ K₀ m₀ : ℕ)
      (k : ℕ → ℕ) (E : ∀ m, SubspaceEvasion312.Explicit.Vec F (k m) →ₗ[F] SubspaceEvasion312.Explicit.Blocks F s m)
      (dim entry : SubspaceEvasion312.Explicit.Program F), 0 < K₀ →
      (∀ m ≥ m₀, k m ≤ s * m) →
      (∀ m ≥ m₀,
        SubspaceEvasion312.Explicit.RunsWithin dim [m] [] (K₀ * (m+1)^h₀) (K₀ * (m+1)^h₀) [] [k m] ∧
        ∀ (j : Fin (k m)) (i : Fin m) (u : Fin s),
          SubspaceEvasion312.Explicit.RunsWithin entry [m, j.val, i.val, u.val] []
            (K₀ * (m+1)^h₀) (K₀ * (m+1)^h₀)
            [E m (Pi.single j 1) i u]) →
      ∃ (gen enc : SubspaceEvasion312.Explicit.Program F) (m₁ : ℕ), m₀ ≤ m₁ ∧
        SubspaceEvasion312.Explicit.CodeAlgorithms k E gen enc
          (fun m => K₀ * (s+2)^c * (m+1)^(h₀+c))
          (fun m => K₀ * (s+2)^c * (m+1)^(h₀+c)) m₁ := by sorry
