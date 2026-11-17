-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_Supplement_theorem_4_2
-- name    : RollingProbeQN.Convex.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:46:19.548169+00:00
-- url     : https://prove2.me/theorems/c7e38d6b-50fa-48ad-a77d-0e14946d1573
-- title:
--   Theorem 4.2 — SC-RP-QNPE: well defined, three gradients per iteration, moment bound (20), rate (21) and gradient complexity (22)
-- statement:
--   Let $f$ satisfy Assumptions 2.1 and 4.1 ($0\preceq\mu I\preceq H(x)\preceq L_1I$, $L_2$-Lipschitz Hessian, minimizer $x^\star$ with $\|x_0-x^\star\|\le R$, pattern $\mathcal S$ and structurally orthogonal partition into $\chi$ groups), and run Algorithm 2 (SC-RP-QNPE) with Subroutine 2.1 and $b=L_2R$. Write $\kappa=L_1/\mu$, $q=1-\sqrt{\sigma/(\kappa+\sigma)}$, $C_\sharp$ and $T_\sharp$ as in (70), $B_\sharp=C_\sharp/\mu$, $\underline\lambda$ for the smoothness step, and $\mathcal L_\varepsilon=\log_+\frac{L_1R^2}{2\sigma\varepsilon}$.
--
--   For every $\sigma\in(0,1)$ there is a constant $C>0$, depending on $\sigma$ only, such that:
--
--   1. every iteration queries the oracle at most three times, at the listed points only (two oracles agreeing at all queries before iteration $k$ give the same state at iteration $k$);
--   2. the method is well defined: at every executed iteration $\underline\lambda\le\bar\lambda_k$, the bisection ends with bracket ratio at most $2^{1/4}$, and $\lambda_k>0$; every step satisfies (16), $\|r_k+\lambda_k\nabla f(x_{k+1})\|\le\sigma\sqrt{1+\mu\lambda_k}\,\|r_k\|$; and $\lambda_k\ge\underline\lambda\ge\sigma/L_1$;
--   3. for every $N\ge1$ with iterations $0,\dots,N-1$ executed,
--   $$\sum_{k<N}\frac{\sqrt{1+\mu\lambda_k}}{\lambda_k}\le C_\sharp ; \tag{20}$$
--   4. for every $N\ge1$, with $n=N-1$,
--   $$f(x_N)-f^\star\le\frac{L_1R^2}{2\sigma}\min\Big\{q^n,\Big(1+\frac{n^2}{B_\sharp^2}\Big)^{-n},\exp\Big(-\frac1{\sqrt2}\min\Big\{\frac n2,\Big(\frac n2\Big)^{3/2}B_\sharp^{-1/2}\Big\}\Big)\Big\};\tag{21}$$
--   5. for every $0<\varepsilon<L_1R^2/2$, the $\varepsilon$-run returns an $\varepsilon$-accurate point after at most
--   $$C\Big(1+\min\Big\{\sqrt\kappa\,\mathcal L_\varepsilon,\ \mathcal L_\varepsilon+(B_\sharp\mathcal L_\varepsilon^2)^{1/3},\ \frac{\mathcal L_\varepsilon}{\log(1+(\mathcal L_\varepsilon/B_\sharp)^{2/3})}\Big\}\Big)\tag{22}$$
--   oracle calls.
--
--   The three branches of (21) are the accelerated linear rate, a superlinear envelope, and a moderate-accuracy rate; (22) is the corresponding gradient complexity.
--
--   **Formalization Note** The run is a function of the oracle; the theorem takes $G=\nabla f$, $f^\star=f(x^\star)$. After a return at a zero gradient the run without the stopping rule is frozen. $\mu\le L_1$, assumed in Appendix F, follows from the hypotheses since $d\ge1$.
--
--   Differences from the source:
--   - reading: O_σ(·) in (22) → ∃ C > 0 chosen after σ and before d, χ, f, L₁, L₂, R, μ, ε; reason: the proof (§F.7, pp. 62–63) gives at most 4 + 3n_ε queries with constants depending on σ only (base reading R1)
--   - reading: "uses at most three gradients per iteration" → each iteration's query list has length ≤ 3, and two oracles agreeing on all queries before iteration k give the same state; reason: a count of oracle calls is meaningful only with oracle locality (base reading R3)
--   - reading: "is well defined" → at every executed iteration λ̲ ≤ λ̄_k, the returned bracket has ratio ≤ 2^{1/4}, and λ_k > 0; reason: these are the properties that make Subroutine 2.1 a terminating, positive stepsize rule (pp. 14, 16)
--   - generalization: (21) after every completed iteration N ≥ 1 → (21) for every N ≥ 1 on the run frozen after a return at ∇f(x_k) = 0; reason: after such a return x_k is the minimizer, so f(x_N) − f★ = 0; on completed iterations it is the paper's statement (base reading R2)
--   - encoding: (20) for every N ≥ 1 → (20) for every N ≥ 1 whose iterations 0, …, N − 1 are executed; reason: λ_k exists only at executed iterations (base reading R2)
--   - encoding: the while loop of Subroutine 2.1 → a guarded bisection pass iterated ⌈4 log(λ̄_k/λ̲)/log 2⌉ + 1 times; reason: the claim "the returned bracket has ratio ≤ 2^{1/4}" shows this is at least the loop's length (base reading R8)
--   - encoding: groups g_1, …, g_χ, i_k = (k mod χ) + 1 → 0-based labels k % χ, partition into χ ≥ 1 nonempty groups (published Assumption21); reason: base readings R5, R7
--   - encoding: gradient count → length of the oracle query list, including the initial query at x₀; reason: base reading R4
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Theorem 4.2, p. 15 (constants (70), p. 52; proof Appendix F, pp. 52–63)

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Assumption21
import Definitions.Def_RollingProbeQN_Convex_Supplement_Assumptions
import Definitions.Def_RollingProbeQN_Convex_Supplement_SCAlgorithm
import Definitions.Def_RollingProbeQN_Convex_Supplement_SCConstants

namespace RollingProbeQN.Convex.Supplement

/-- **Theorem 4.2 (SC-RP-QNPE: well-posedness, moment bound, rate and gradient complexity).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Theorem 4.2, p. 15: "Under Assumptions 2.1
and 4.1, Algorithm 2 with Subroutine 2.1 is well defined, uses at most three gradients per iteration,
every step satisfies (16), `λk ≥ λ ≥ σ/L1`, and `∑_{k<N} √(1 + μλk)/λk ≤ C♯` for every `N ≥ 1`. (20)
Consequently, after every completed iteration `N ≥ 1`, with `n = N − 1`,
`f(xN) − f★ ≤ L1R²/(2σ) min{q^n, (1 + n²/B♯²)^{−n}, exp(−1/√2 min{n/2, (n/2)^{3/2} B♯^{−1/2}})}`, (21)
and, for `0 < ε < L1R²/2`, the method returns an `ε`-accurate point after `Gε` gradient queries, where
`Gε = Oσ(1 + min{√κ Lε, Lε + (B♯Lε²)^{1/3}, Lε/log(1 + (Lε/B♯)^{2/3})})`. (22)"

Notation (pp. 13, 15, 52): `κ = L₁/μ`, `Lε = log₊(L₁R²/(2σε))`, `q = 1 − √(σ/(κ + σ))`,
`C♯ = (2/σ)[χL₁ + 2L₂R + (2χ + 1)L₂R T♯]` and `B♯ = C♯/μ` with `T♯` of (70); `λ` (underlined) is the
smoothness step `λ̲`, the positive root of `λL₁ = σ√(1 + μλ)`; (16) is
`‖r_k + λ_k∇f(x_{k+1})‖ ≤ σ√(1 + μλ_k)‖r_k‖`.

For every `σ ∈ (0, 1)` there is `C > 0` such that, for all data satisfying Assumptions 2.1 and 4.1, the
run of Algorithm 2 with `b = L₂R`:
1. calls the oracle at most three times per iteration, at the listed points only (for every oracle `G`
   the query list of each iteration has length at most 3, and two oracles that agree at every query made
   before iteration `k` produce the same state at iteration `k`);
2. is well defined: at every executed iteration the initial bracket is valid (`λ̲ ≤ λ̄_k`), the
   bisection ends (the returned bracket has ratio at most `2^{1/4}`) and `λ_k > 0`; every step satisfies
   (16); `λ_k ≥ λ̲`; and `λ̲ ≥ σ/L₁`;
3. satisfies (20) for every `N ≥ 1` such that iterations `0, …, N − 1` are executed;
4. satisfies (21) for every `N ≥ 1`;
5. for `0 < ε < L₁R²/2`, with target `ε`, returns at some iteration `k` (its first return) an
   `ε`-accurate point after at most `C(1 + min{…})` oracle calls, the minimum of (22).

**Formalization Note.** Reading R1 of the base mission: `O_σ` is a constant `C` chosen after `σ` and
before all the data (the proof, §F.7, p. 63, gives at most `4 + 3n_ε` queries with `n_ε` explicit).
Reading R2: the run without the stopping rule of Step 5 is frozen after a return at a zero gradient,
where `x_k` is the minimizer; (21) is stated for this run at every `N ≥ 1`, (22) for the ε-run. Reading
R3: the run is a function of the oracle `G`. Reading R4: the count includes the initial query. `f★` is
`f x★`. `μ ≤ L₁` (assumed in Appendix F, p. 53) follows from the hypotheses, since `d ≥ 1`. -/
theorem theorem_4_2 :
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (d χ : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (L₁ L₂ R μ : ℝ) (S : Set (Fin d × Fin d))
        (grp : Fin d → Fin χ) (x₀ xstar : EuclideanSpace ℝ (Fin d)),
        Assumption21 d χ f L₁ L₂ R S grp x₀ xstar → Assumption41 f μ →
        let cfg : Config d χ := ⟨grp, S, L₁, L₂, L₂ * R, σ⟩
        let κ : ℝ := L₁ / μ
        let q : ℝ := 1 - Real.sqrt (σ / (κ + σ))
        let Cs : ℝ := Csharp σ μ χ L₁ L₂ R
        let Bs : ℝ := Cs / μ
        let lamLow : ℝ := rootSC L₁ σ μ
        (∀ (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (k : ℕ),
          (scIterQueries cfg μ R G x₀ k).length ≤ 3) ∧
        (∀ (G G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (k : ℕ),
          (∀ p ∈ scAllQueries cfg μ R G x₀ k, G p = G' p) →
            scRun cfg μ R G x₀ k = scRun cfg μ R G' x₀ k) ∧
        σ / L₁ ≤ lamLow ∧
        (∀ k : ℕ, scActive cfg μ R (gradient f) x₀ k →
          lamLow ≤ (scIterAt cfg μ R (gradient f) x₀ k).lamBar ∧
          (scIterAt cfg μ R (gradient f) x₀ k).lamPlus / (scIterAt cfg μ R (gradient f) x₀ k).lam
            ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) ∧
          0 < (scIterAt cfg μ R (gradient f) x₀ k).lam ∧
          ‖(scIterAt cfg μ R (gradient f) x₀ k).r +
              (scIterAt cfg μ R (gradient f) x₀ k).lam •
                gradient f (scIterAt cfg μ R (gradient f) x₀ k).x'‖ ≤
            σ * Real.sqrt (1 + μ * (scIterAt cfg μ R (gradient f) x₀ k).lam) *
              ‖(scIterAt cfg μ R (gradient f) x₀ k).r‖ ∧
          lamLow ≤ (scIterAt cfg μ R (gradient f) x₀ k).lam) ∧
        (∀ N : ℕ, 1 ≤ N → (∀ k < N, scActive cfg μ R (gradient f) x₀ k) →
          ∑ k ∈ Finset.range N,
              Real.sqrt (1 + μ * (scIterAt cfg μ R (gradient f) x₀ k).lam) /
                (scIterAt cfg μ R (gradient f) x₀ k).lam ≤ Cs) ∧
        (∀ N : ℕ, 1 ≤ N →
          f (scRun cfg μ R (gradient f) x₀ N).x - f xstar ≤
            L₁ * R ^ 2 / (2 * σ) *
              min (q ^ (N - 1))
                (min (((1 + ((N - 1 : ℕ) : ℝ) ^ 2 / Bs ^ 2) ^ (N - 1))⁻¹)
                  (Real.exp (-(1 / Real.sqrt 2) *
                    min (((N - 1 : ℕ) : ℝ) / 2)
                      ((((N - 1 : ℕ) : ℝ) / 2) ^ ((3 : ℝ) / 2) * Bs ^ (-(1 : ℝ) / 2)))))) ∧
        (∀ ε : ℝ, 0 < ε → ε < L₁ * R ^ 2 / 2 →
          let Lε : ℝ := max 0 (Real.log (L₁ * R ^ 2 / (2 * σ * ε)))
          ∃ k : ℕ,
            scEpsReturns cfg μ R (gradient f) x₀ ε k ∧
            (∀ j < k, ¬ scEpsReturns cfg μ R (gradient f) x₀ ε j) ∧
            f (scEpsOutput cfg μ R (gradient f) x₀ k) - f xstar ≤ ε ∧
            ((scAllQueries cfg μ R (gradient f) x₀ (k + 1)).length : ℝ) ≤
              C * (1 + min (Real.sqrt κ * Lε)
                (min (Lε + (Bs * Lε ^ 2) ^ ((1 : ℝ) / 3))
                  (Lε / Real.log (1 + (Lε / Bs) ^ ((2 : ℝ) / 3)))))) := by sorry

end RollingProbeQN.Convex.Supplement
