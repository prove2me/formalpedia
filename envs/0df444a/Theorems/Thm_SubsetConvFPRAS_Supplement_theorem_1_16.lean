-- Prove2me | Theorems.Thm_SubsetConvFPRAS_Supplement_theorem_1_16
-- name    : SubsetConvFPRAS.Supplement.theorem_1_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:49:19.920195+00:00
-- url     : https://prove2.me/theorems/112cad5e-c5ec-4286-ab4e-f36fc14abc11
-- title:
--   Theorem 1.16 — FPRAS for $Z_\alpha$ under downward closed supports and spectral curvatures $\eta+\kappa\ge0$
-- statement:
--   Let $\mu,\nu:2^U\to\mathbb R_{\ge0}$, $|U|=n$, have downward closed supports and upward spectral curvatures $\eta,\kappa$ (Definition 1.10) with $\eta+\kappa\ge0$, and let $0<\varepsilon<1$. Put $\gamma=\max\{\eta,\kappa\}$. If $\gamma>0$, let $\chi\ge1$ be a supplied bound with
--   $$\omega(S+u)\le\chi\,\gamma\,\omega(S)\qquad\text{for }\omega\in\{\mu,\nu\},\ S\in\operatorname{supp}\omega,\ u\notin S;$$
--   otherwise take $\chi=1$. Given $\eta,\kappa$, value oracles for $\mu,\nu$, upper bounds $R_\mu,R_\nu$ on the coefficient ranges (2), and $\varepsilon$, there is an FPRAS for every coefficient
--   $$Z_\alpha=[x^\alpha]\bigl(g_\mu(x)\,g_\nu(x)\bigr),\qquad\alpha\in\{0,1,2\}^U,$$
--   using at most
--   $$\tilde O\Bigl(\frac{n^{11}(n+\log(R_\mu R_\nu))^2}{\varepsilon^2}+\frac{n^5\chi\,(n+\log(R_\mu R_\nu))}{\varepsilon^3}\Bigr)$$
--   arithmetic operations and evaluation oracle calls.
--
--   Precisely: there are one program $P$ of the arithmetic model and constants $C,K$ such that for every instance, with $\Lambda=n+1+\log(R_\mu R_\nu)$, $\chi_{\mathrm{eff}}=\chi$ if $\gamma>0$ and $1$ otherwise, and
--   $$B=\Bigl\lceil C\Bigl((n+1)^{11}\Lambda^2\varepsilon^{-2}+(n+1)^5\chi_{\mathrm{eff}}\Lambda\varepsilon^{-3}\Bigr)\log^K(2+\Lambda+\varepsilon^{-1})\Bigr\rceil,$$
--   every run halts within $B$ steps with an output $\hat Z\ge0$, and on at least $3/4$ of the $B$-bit coin tapes $(1-\varepsilon)Z_\alpha\le\hat Z\le(1+\varepsilon)Z_\alpha$.
--
--   The theorem generalizes Theorem 1.6 beyond log-concave weights (Remark 1.17): no log-concavity and no starting sets are needed, and the threshold $\eta+\kappa\ge0$ is optimal among constant thresholds (Remark 1.18).
--
--   **Formalization Note** Input layout: integer cell $0$ holds $n$, cell $1+u$ holds $\alpha_u$; real cells $0,\dots,5$ hold $\varepsilon,R_\mu,R_\nu,\eta,\kappa,\chi$.
--
--   Differences from the source:
--   - reading: an unnamed randomness primitive of the arithmetic model → fair coins only, one tape bit per coin instruction; reason: as in the published Theorem 1.6: a unit-cost uniform real would be a stronger machine and so a weaker theorem
--   - encoding: an algorithm in the arithmetic model using O(·) operations and oracle calls → one admissible program of the published unit-cost real RAM, with C, K chosen before the instance and work counted per executed instruction; reason: the model of Theorem 1.6 (p.44); every instruction costs 1
--   - reading: "uses at most" Õ(·) operations → every run, on every coin tape, halts within the bound; reason: the proof bounds the cost "on every execution" (p.37)
--   - encoding: Õ(n¹¹(n + log(R_μR_ν))²/ε² + n⁵χ(n + log(R_μR_ν))/ε³) → C((n+1)¹¹Λ²ε⁻² + (n+1)⁵χ_eff Λ ε⁻³)·log^K(2 + Λ + ε⁻¹) with Λ = n + 1 + log(R_μR_ν) and χ_eff = χ if γ > 0, else 1; reason: (n+1) and Λ are within constant factors of n and n + log(R_μR_ν) for n ≥ 1 and cover U = ∅; the log base exceeds 1; the proof's log factors (pp.36–37) involve n, ε, R_μ, R_ν only
--   - generalization: χ ≥ 1 a supplied bound "polynomial in n and ε⁻¹" → any real χ ≥ 1 (when γ > 0), χ appearing explicitly in the bound; reason: for χ polynomial in n and ε⁻¹ this is exactly the source's bound; the proof's cost (p.37) is linear in χ and uses no polynomiality of χ
--   - reading: "In all other cases, take χ = 1 without imposing this bound" → χ is still a real input; when γ ≤ 0 neither χ ≥ 1 nor the growth bound is assumed, and the bound uses 1 in place of χ; reason: the source's case split, with the input slot kept so that one program serves every instance
--   - generalization: upward spectral curvature (Definition 1.10) is defined for weights that are not identically zero → μ or ν may be identically zero (then the curvature hypothesis is vacuous and Z_α = 0); reason: the case μ(C)ν(C) = 0 gives Z_α = 0 (App. A.1, p.35); for nonzero weights the statement is the source's
--   - encoding: upper bounds on R_μ, R_ν → reals R_μ, R_ν ≥ 1 with RangeLE μ R_μ and RangeLE ν R_ν; reason: R_ω ≥ 1 by (2), p.4, and p.4 allows upper bounds in place of R_ω; 1 ≤ R only binds for a zero weight, where (2) is undefined
--   - encoding: Pr[(1−ε)Z_α ≤ Ẑ ≤ (1+ε)Z_α] ≥ 3/4 and Ẑ ≥ 0 → at least 3/4 of the B-bit tapes give an output in the interval, and the output is ≥ 0 on every tape; reason: a run of B steps reads at most B coins, so counting B-bit tapes is the fair-coin probability
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Theorem 1.16, p.7; Definition 1.1, p.3; (2), p.4; proof in Appendix A.1, pp.35–37

import Mathlib
import Definitions.Def_SubsetConvFPRAS_SetWeights
import Definitions.Def_SubsetConvFPRAS_Machine
import Definitions.Def_SubsetConvFPRAS_Supplement_CurvatureInput

open scoped Classical

namespace SubsetConvFPRAS.Supplement

open SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Theorem 1.16, p.7, with Definition 1.1, p.3. Let
`μ, ν` have downward closed supports and upward spectral curvatures `η, κ` with `η + κ ≥ 0`, and fix
`0 < ε < 1`. Put `γ = max{η, κ}`; if `γ > 0`, let `χ ≥ 1` be a supplied bound with
`ω(S + u) ≤ χ γ ω(S)` for `ω ∈ {μ, ν}`, `S ∈ supp ω`, `u ∉ S`; otherwise take `χ = 1`. Given `η, κ`, value
oracles for `μ, ν`, upper bounds on `R_μ, R_ν`, and `ε`, there is an FPRAS for every coefficient
`Z_α = [x^α](g_μ g_ν)`, `α ∈ {0,1,2}^U`, using at most
`Õ(n¹¹(n + log(R_μR_ν))²/ε² + n⁵χ(n + log(R_μR_ν))/ε³)` arithmetic operations and oracle calls.

**Formalization Note.** One program `P`, with the constants `C, K` of the `Õ`, is chosen before the
instance; the input layout is `initCurvature`. `χ_eff = if 0 < γ then χ else 1` enters the bound; the
growth bound and `χ ≥ 1` are assumed only when `γ > 0`. `χ` is not required to be polynomial: it appears
in the bound. `(n+1)` replaces `n` and `Λ = n + 1 + log(R_μR_ν)` replaces `n + log(R_μR_ν)`; the base of
the polylogarithm exceeds `1`. Upper bounds on `R_ω` are reals `R ≥ 1` with `RangeLE ω R`. The bound
holds on every tape, the output is nonnegative on every tape, and probability is by counting tapes. -/
theorem theorem_1_16 :
    ∃ (P : Program) (C K : ℕ), Admissible P ∧
      ∀ (n : ℕ) (μ ν : Finset (Fin n) → ℝ), (∀ S, 0 ≤ μ S) → (∀ S, 0 ≤ ν S) →
        HasDownwardClosedSupport μ → HasDownwardClosedSupport ν →
      ∀ (η κ : ℝ), HasCurv μ η → HasCurv ν κ → 0 ≤ η + κ →
      ∀ (χ : ℝ), (0 < max η κ → 1 ≤ χ ∧
          (∀ S, 0 < μ S → ∀ u, u ∉ S → μ (insert u S) ≤ χ * max η κ * μ S) ∧
          (∀ S, 0 < ν S → ∀ u, u ∉ S → ν (insert u S) ≤ χ * max η κ * ν S)) →
      ∀ (Rμ Rν : ℝ), RangeLE μ Rμ → 1 ≤ Rμ → RangeLE ν Rν → 1 ≤ Rν →
      ∀ (α : Fin n → Fin 3) (ε : ℝ), 0 < ε → ε < 1 →
        let χe : ℝ := if 0 < max η κ then χ else 1
        let Λ : ℝ := (n : ℝ) + 1 + Real.log (Rμ * Rν)
        let B : ℕ := ⌈(C : ℝ) * (((n : ℝ) + 1) ^ 11 * Λ ^ 2 * (ε⁻¹) ^ 2 +
            ((n : ℝ) + 1) ^ 5 * χe * Λ * (ε⁻¹) ^ 3) * (Real.log (2 + Λ + ε⁻¹)) ^ K⌉₊
        let s₀ := initCurvature α ε Rμ Rν η κ χ
        (∀ ω : ℕ → Bool, ∃ z : ℝ,
          (run P μ ν s₀ ω B).output = some z ∧ 0 ≤ z ∧ (run P μ ν s₀ ω B).work ≤ B) ∧
        (3 / 4 : ℝ) * 2 ^ B ≤
          (tapeCount P μ ν s₀ B (fun st => ∃ z : ℝ, st.output = some z ∧
            (1 - ε) * coeffZ μ ν α ≤ z ∧ z ≤ (1 + ε) * coeffZ μ ν α) : ℝ) := by sorry

end SubsetConvFPRAS.Supplement
