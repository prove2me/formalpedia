-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_constant_alphabet_design_entries
-- name    : SubspaceEvasion312.Explicit.constant_alphabet_design_entries
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:52:49.449833+00:00
-- url     : https://prove2.me/theorems/2b1066c2-72bb-4b10-99d3-ed6ca98d4e6c
-- title:
--   Theorem 17 — constant-alphabet designs with uniform generator-matrix entries
-- statement:
--   There are absolute integers $A>0,a,h$ with the following property. For every finite field $F_q$, rank $r$, and $0<\varepsilon\le1$, there is a multiplier $K>0$ independent of the target rate $R$. For every $R>0$ with $R+\varepsilon\le1$, there is an explicit family $C_m\le(F_q^s)^m$ of additive codes for all sufficiently large $m$, with
--   \[
--   0<s\le A(1+r+1/\varepsilon)^a q^{r^2},\qquad \operatorname{rate}(C_m)\ge R,
--   \]
--   and a subspace-design function $\tau_m$ satisfying $\tau_m(r)\le R+\varepsilon$. The dimension-correct linear encoder $E_m:F_q^{k_m}\to(F_q^s)^m$ has image $C_m$.
--
--   Effectivity is presented by two fixed programs: one computes $k_m$ from $m$, and the other computes each generator-matrix entry $E_m(e_j)_{i,u}$ from $(m,j,i,u)$. Both have time and natural-register bound $K(m+1)^h$, including setup. Also $k_m\le sm$. The multiplier $K$ does not depend on $R$, although $s$ and the threshold $m_0$ may.
--
--   This is the cited Goyal–Guruswami–Hsieh construction, with its explicit linear-code conclusion represented at the generator-matrix level. A generic compilation lemma turns this presentation into basis generation and encoding programs.
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 17 [GGH26], printed p.10 (PDF p.11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc. The generator-matrix programs are the operational representation of the stated explicit linear codes; the dimension bound follows from k_m = dim C_m <= sm.

import Definitions.Def_SubspaceEvasion312_Explicit_effective

/-- Theorem 17 with its explicit generator matrix presented by uniform programs. -/
theorem SubspaceEvasion312.Explicit.constant_alphabet_design_entries :
    ∃ A a h : ℕ, 0 < A ∧
    ∀ (F : Type) [Field F] [Fintype F] (r : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ K : ℕ, 0 < K ∧
    ∀ R : ℝ, 0 < R → R + ε ≤ 1 →
    ∃ (s m₀ : ℕ) (C : ∀ m, SubspaceEvasion312.Explicit.Code F s m) (k : ℕ → ℕ)
      (E : ∀ m, SubspaceEvasion312.Explicit.Vec F (k m) →ₗ[F] SubspaceEvasion312.Explicit.Blocks F s m)
      (τ : ℕ → ℕ → ℝ) (dim entry : SubspaceEvasion312.Explicit.Program F),
      0 < s ∧ 0 < m₀ ∧ (s : ℝ) ≤ A * (1 + r + 1 / ε)^a * (Fintype.card F : ℝ)^(r^2) ∧
      (∀ m ≥ m₀, k m ≤ s * m) ∧
      (∀ m ≥ m₀,
        SubspaceEvasion312.Explicit.RunsWithin dim [m] [] (K * (m+1)^h) (K * (m+1)^h) [] [k m] ∧
        ∀ (j : Fin (k m)) (i : Fin m) (u : Fin s),
          SubspaceEvasion312.Explicit.RunsWithin entry [m, j.val, i.val, u.val] []
            (K * (m+1)^h) (K * (m+1)^h) [E m (Pi.single j 1) i u]) ∧
      ∀ m ≥ m₀, SubspaceEvasion312.Explicit.IsEncoder (C m) (E m) ∧
        R ≤ SubspaceEvasion312.Explicit.codeRate (C m) ∧
        SubspaceEvasion312.Explicit.SubspaceDesign (C m) (τ m) ∧ τ m r ≤ R + ε := by sorry
