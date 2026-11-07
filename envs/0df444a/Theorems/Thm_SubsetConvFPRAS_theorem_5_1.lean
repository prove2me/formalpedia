-- Prove2me | Theorems.Thm_SubsetConvFPRAS_theorem_5_1
-- name    : SubsetConvFPRAS.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:12.81755+00:00
-- url     : https://prove2.me/theorems/e0bc63bf-d476-48e1-9223-80876e780410
-- title:
--   Theorem 5.1 — FPRAS for $Z_\cap=\sum_S\mu(S)\nu(U\setminus S)$ for homogeneous log-concave $\mu,\nu$
-- statement:
--   Let $\mu,\nu:2^U\to\mathbb R_{\ge0}$ be supported on $\binom Ua$ and $\binom Ub$, with $a+b=n=|U|\ge1$, and let $g_\mu,g_\nu$ be log-concave. Given value oracles for $\mu,\nu$, upper bounds $R_\mu,R_\nu$ on the coefficient ranges (2), sets $S_0,T_0$ with $\mu(S_0)>0$, $\nu(T_0)>0$, and $0<\varepsilon\le1$, there is an FPRAS for
--   $$Z_\cap=[x^U](g_\mu g_\nu)=\sum_{S\subseteq U}\mu(S)\nu(U\setminus S)\tag{17}$$
--   that on every execution uses at most
--   $$O\Bigl(n^{10}(n+\log R_\mu R_\nu)^2\varepsilon^{-2}\log^2\frac{2(n+\log R_\mu R_\nu)}{\varepsilon}\Bigr)\tag{18}$$
--   arithmetic operations and value-oracle calls. Precisely: one program and one constant $C$ such that every run halts within that bound with a nonnegative output, which is $0$ whenever $Z_\cap=0$, and on at least $3/4$ of the tapes the output $\hat Z$ satisfies $(1-\varepsilon)Z_\cap\le\hat Z\le(1+\varepsilon)Z_\cap$.
--
--   Theorem 1.6 is obtained by applying this to each pair of homogeneous layers.
--
--   **Formalization Note** Input: integer cell $0$ holds $n$, bitmaps $0,1$ hold $S_0,T_0$, real cells $0,1,2$ hold $\varepsilon,R_\mu,R_\nu$. The degrees $a,b$ are not given: they are $|S_0|,|T_0|$.
--
--   Differences from the source:
--   - generalization: the coefficient ranges R_μ, R_ν → any upper bounds R_μ, R_ν (RangeLE), with the bound in terms of them; reason: p.4 allows user-supplied upper bounds "with the same replacement in the running-time bounds"; R = the true range is a special case
--   - reading: an unnamed randomness primitive ("chooses with probability p") → fair coins only, one tape bit per coin instruction; reason: the page names no primitive for its arithmetic model; a unit-cost uniform real would be a stronger machine and so a weaker theorem
--   - encoding: an algorithm in the arithmetic model, O(·) operations and oracle calls → one admissible program of the unit-cost real RAM, with the constant C chosen before the instance and work counted per executed instruction; reason: the paper's model (p.44); every instruction costs 1, which only adds to the count
--   - generalization: an FPRAS (Definition 1.1) → also: the output is 0 on every tape when Z_∩ = 0; reason: the proof shows it (p.26: "every execution returns zero"); it is what lets Theorem 1.6 sum layers, and dropping it gives the source's claim
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Theorem 5.1, pp.20–21 (proof pp.25–26)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_PairLaws
import Definitions.Def_SubsetConvFPRAS_Machine

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Theorem 5.1, pp.20–21. There is an FPRAS for
`Z_∩ = ∑_{S ⊆ U} μ(S) ν(U∖S)`, (17), for homogeneous log-concave `μ, ν` of degrees `a + b = n ≥ 1`. For every
`0 < ε ≤ 1` it uses at most `O(n¹⁰ (n + log(R_μ R_ν))² ε⁻² log²(2(n + log(R_μ R_ν))/ε))` operations and oracle calls on
every execution, (18).

**Formalization Note.** One program, chosen with `C` before the instance. The input layout is `initConvolution`. `R_μ,
R_ν` may be upper bounds (p.4). The clause `Z_∩ = 0 → z = 0` on every tape is what the proof shows on p.26. -/
theorem theorem_5_1 :
    ∃ (P : Program) (C : ℕ), Admissible P ∧
      ∀ (n a b : ℕ) (μ ν : Finset (Fin n) → ℝ), IsHomogeneousPair a b μ ν →
      ∀ (S₀ T₀ : Finset (Fin n)) (Rμ Rν ε : ℝ), 0 < μ S₀ → 0 < ν T₀ →
        RangeLE μ Rμ → RangeLE ν Rν → 0 < ε → ε ≤ 1 →
        let Λ : ℝ := (n : ℝ) + Real.log (Rμ * Rν)
        let B : ℕ := ⌈(C : ℝ) * (n : ℝ) ^ 10 * Λ ^ 2 * (ε⁻¹) ^ 2 * (Real.log (2 * Λ / ε)) ^ 2⌉₊
        let s₀ := initConvolution S₀ T₀ ε Rμ Rν
        (∀ ω : ℕ → Bool, ∃ z : ℝ,
          (run P μ ν s₀ ω B).output = some z ∧ 0 ≤ z ∧ (run P μ ν s₀ ω B).work ≤ B ∧
            (subsetConvTop μ ν = 0 → z = 0)) ∧
        (3 / 4 : ℝ) * 2 ^ B ≤
          (tapeCount P μ ν s₀ B (fun st => ∃ z : ℝ, st.output = some z ∧
            (1 - ε) * subsetConvTop μ ν ≤ z ∧ z ≤ (1 + ε) * subsetConvTop μ ν) : ℝ) := by sorry

end SubsetConvFPRAS
