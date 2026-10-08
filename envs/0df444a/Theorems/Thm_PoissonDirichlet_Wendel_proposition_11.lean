-- Prove2me | Theorems.Thm_PoissonDirichlet_Wendel_proposition_11
-- name    : PoissonDirichlet.Wendel.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:00.623457+00:00
-- url     : https://prove2.me/theorems/74404ae0-b077-4a2f-bdf6-79f15ba9bbeb
-- title:
--   Proposition 11, pp. 863–864 — 1/V_n = 1 + A_{n−1} + Σ_n with independent A_{n−1}, Σ_n of Laplace transforms φ_α^{n−1}, ψ_α^{−n}
-- statement:
--   Let $0<\alpha<1$ and let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ distribution. Let $A_0=0$ and, for $n\ge1$,
--   $$A_n=\frac{V_1+\cdots+V_n}{V_{n+1}},\qquad\Sigma_n=\frac{V_{n+1}+V_{n+2}+\cdots}{V_n},$$
--   and let $\phi_\alpha,\psi_\alpha$ be as in (33)–(34). Then for every $n\ge1$
--   $$\frac1{V_n}=1+A_{n-1}+\Sigma_n\quad\text{a.s.},$$
--   where:
--
--   1. (i) $A_{n-1}$ is distributed as the sum of $n-1$ independent copies of $A_1$, with $E[\exp(-\lambda A_{n-1})]=\phi_\alpha(\lambda)^{n-1}$ for all $\lambda\ge0$;
--   2. (ii) $\Sigma_n$ is distributed as the sum of $n$ independent copies of $\Sigma_1$, with $E[\exp(-\lambda\Sigma_n)]=\psi_\alpha(\lambda)^{-n}$ for all $\lambda\ge0$;
--   3. (iii) $A_{n-1}$ and $\Sigma_n$ are independent.
--
--   This decomposition gives Wendel's formula (38) for the Laplace transform of $1/V_n$ (Corollary 12) and underlies the later computations of the paper.
--
--   **Formalization Note** 0-based: for `k : ℕ`, `V ω k` is $V_{k+1}$, `Aseq (V ω) k` is $A_k$ and `Sigseq (V ω) k` is $\Sigma_{k+1}$, so the exponents are $k$ and $k+1$. "Distributed as the sum of $m$ independent copies of $X$" is stated as: the law equals the $m$-fold convolution power of the law of $X$ (the Dirac mass at $0$ for $m=0$, matching $A_0=0$). Expectations are Bochner integrals of functions with values in $(0,1]$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), pp. 863–864, Proposition 11, (31)–(37)

import Mathlib
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Wendel

/-- Proposition 11, pp. 863–864: for `V` with law PD(α, 0), 0 < α < 1, and n = k + 1 ≥ 1:
(35) `1/V_n = 1 + A_{n-1} + Σ_n` a.s.; (i) `A_{n-1}` is distributed as the sum of n − 1
independent copies of `A_1`, with (36) `E[exp(-λ A_{n-1})] = φ_α(λ)^{n-1}`; (ii) `Σ_n` is
distributed as the sum of n independent copies of `Σ_1`, with (37)
`E[exp(-λ Σ_n)] = ψ_α(λ)^{-n}`; (iii) `A_{n-1}` and `Σ_n` are independent.
0-based: `V ω k` is `V_n`, `Aseq (V ω) k` is `A_{n-1}`, `Sigseq (V ω) k` is `Σ_n`. -/
theorem proposition_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) (k : ℕ) :
    (∀ᵐ ω ∂P, 1 / V ω k = 1 + Aseq (V ω) k + Sigseq (V ω) k) ∧
    HasLaw (fun ω => Aseq (V ω) k) (convPow (P.map fun ω => Aseq (V ω) 1) k) P ∧
    (∀ l : ℝ, 0 ≤ l → ∫ ω, Real.exp (-l * Aseq (V ω) k) ∂P = phi α l ^ k) ∧
    HasLaw (fun ω => Sigseq (V ω) k) (convPow (P.map fun ω => Sigseq (V ω) 0) (k + 1)) P ∧
    (∀ l : ℝ, 0 ≤ l → ∫ ω, Real.exp (-l * Sigseq (V ω) k) ∂P = (psi α l ^ (k + 1))⁻¹) ∧
    IndepFun (fun ω => Aseq (V ω) k) (fun ω => Sigseq (V ω) k) P := by sorry

end PoissonDirichlet.Wendel
