-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_Supplement_theorem_G_1
-- name    : RollingProbeQN.Convex.Supplement.theorem_G_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:47:03.219641+00:00
-- url     : https://prove2.me/theorems/ff9ddcda-3b90-4828-9d91-aeb7fe05fcea
-- title:
--   Theorem G.1 — restarted RP-QNPE returns $w_S$ with $f(w_S)-f^\star\le\varepsilon$ using the gradient count (74)
-- statement:
--   Let $f$ satisfy Assumptions 2.1 and 4.1 and let $\varepsilon>0$. Run the restart scheme: stages $s=0,\dots,S-1$, $S=\max\{0,\lceil\log_2(R\sqrt{L_1/(2\varepsilon)})\rceil\}$, where stage $s$ runs Algorithm 1 from $w_s$ ($w_0=x_0$) with $R_s=2^{-s}R$, $\varepsilon_s=\mu R_s^2/8$, $b=L_2R_s$ and a fresh model, and returns $w_{s+1}$ at its first return. Write $\kappa=L_1/\mu$, $\kappa_2=L_2R/\mu$ and $\mathcal S_\varepsilon=1+\log_+(L_1R^2/\varepsilon)$.
--
--   For every $\sigma\in(0,1)$ there is $C>0$, depending on $\sigma$ only, such that, with the exact gradient oracle:
--
--   1. every stage $s<S$ returns;
--   2. $f(w_S)-f^\star\le\varepsilon$;
--   3. the total number of gradient queries of the $S$ stages satisfies
--   $$G_\varepsilon\le C\Big(\mathcal S_\varepsilon+\min\big\{\sqrt\kappa\,\mathcal S_\varepsilon,\ (\chi\kappa)^{1/3}\mathcal S_\varepsilon+(\chi\kappa_2)^{1/3}\big\}\Big);\tag{74}$$
--   4. any oracle that agrees with $\nabla f$ at every query of the scheme yields the same final point $w_S$.
--
--   Theorem G.1 is the comparison point for Theorem 4.2: restarting the convex method pays the stage costs linearly in $\mathcal S_\varepsilon$.
--
--   **Formalization Note** Each stage is the published run of Algorithm 1 with its published return rule, returned point and query list; each stage's count includes its initial query at $w_s$. When $S=0$ no query is made and $w_S=x_0$.
--
--   Differences from the source:
--   - reading: O_σ(·) in (74) → ∃ C > 0 chosen after σ and before all the data; reason: the proof (p. 65) gives G_ε ≤ 4S + 3min{4S√(κ/σ), S D_σ(4χκ)^{1/3} + 4.85 D_σ(4χκ₂)^{1/3}} with S ≤ S_ε (base reading R1)
--   - reading: "the restart scheme returns a point … using G_ε gradient queries" → every stage returns, f(w_S) − f★ ≤ ε, the scheme's query list has length ≤ the bound, and any oracle agreeing with ∇f on that list gives the same w_S; reason: oracle count with locality (base reading R3)
--   - encoding: "returns w_{s+1} once A_{k+1} ≥ 4/μ" → the least k with the published epsReturns for (R_s, ε_s), whose mass target R_s²/(2ε_s) is 4/μ; a zero-gradient return is included; reason: Step 1 of Algorithm 1 also returns
--   - encoding: S = max{0, ⌈log₂(R√(L₁/(2ε)))⌉} → Nat.ceil of the real logarithm; reason: ⌈t⌉₊ = max{0, ⌈t⌉}
--   - encoding: gradient count → sum over stages of the published allQueries up to the first return, each including its initial query; reason: base reading R4
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Theorem G.1, p. 64 (scheme Appendix G.1, p. 63; proof Appendix G.3, p. 65)

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Assumption21
import Definitions.Def_RollingProbeQN_Convex_Supplement_Assumptions
import Definitions.Def_RollingProbeQN_Convex_Supplement_Restart

namespace RollingProbeQN.Convex.Supplement

/-- **Theorem G.1 (Restarted RP-QNPE).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Theorem G.1, p. 64: "Under Assumptions 2.1
and 4.1, the restart scheme returns a point with `f(wS) − f★ ≤ ε` using
`Gε = Oσ(Sε + min{√κ Sε, (χκ)^{1/3}Sε + (χκ2)^{1/3}})` (74) gradient queries."

The scheme (Appendix G.1, p. 63): stages `s = 0, …, S − 1`, `S = max{0, ⌈log₂(R√(L₁/(2ε)))⌉}`; stage
`s` runs Algorithm 1 from `w_s` (`w_0 = x₀`) with `R_s = 2^{−s}R`, `ε_s = μR_s²/8`, `b = L₂R_s`, a fresh
model, and returns `w_{s+1}` at its first return. Notation (p. 13): `κ = L₁/μ`, `κ₂ = L₂R/μ`,
`Sε = 1 + log₊(L₁R²/ε)`.

For every `σ ∈ (0, 1)` there is `C > 0` such that, for all data satisfying Assumptions 2.1 and 4.1 and
every `ε > 0`, with `G = ∇f`:
1. every stage `s < S` returns;
2. `f(w_S) − f★ ≤ ε`;
3. the total number of oracle calls of the `S` stages is at most
   `C(Sε + min{√κ Sε, (χκ)^{1/3}Sε + (χκ₂)^{1/3}})`;
4. the scheme uses the oracle only at the listed points: any oracle that agrees with `∇f` at every query
   of the scheme gives the same final point `w_S`.

**Formalization Note.** Reading R1 of the base mission: `O_σ` is a constant chosen after `σ` and before
the data; the proof (p. 65) gives `Gε ≤ 4S + 3min{4S√(κ/σ), S D_σ(4χκ)^{1/3} + 4.85 D_σ(4χκ₂)^{1/3}}`.
Each stage is the published `run` of Algorithm 1, with the published `epsReturns`, `epsOutput` and
`allQueries` (reading R4: each stage's count includes its initial query at `w_s`). When `S = 0` no query
is made and `w_S = x₀`. -/
theorem theorem_G_1 :
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (d χ : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (L₁ L₂ R μ : ℝ) (S : Set (Fin d × Fin d))
        (grp : Fin d → Fin χ) (x₀ xstar : EuclideanSpace ℝ (Fin d)) (ε : ℝ),
        Assumption21 d χ f L₁ L₂ R S grp x₀ xstar → Assumption41 f μ → 0 < ε →
        let cfg : Config d χ := ⟨grp, S, L₁, L₂, L₂ * R, σ⟩
        let nS : ℕ := restartStages L₁ R ε
        let κ : ℝ := L₁ / μ
        let κ₂ : ℝ := L₂ * R / μ
        let Sε : ℝ := 1 + max 0 (Real.log (L₁ * R ^ 2 / ε))
        (∀ s < nS, ∃ k : ℕ, epsReturns { cfg with b := L₂ * (R / 2 ^ s) } (gradient f)
            (restartPt cfg R μ (gradient f) x₀ s) (R / 2 ^ s) (μ * (R / 2 ^ s) ^ 2 / 8) k) ∧
        f (restartPt cfg R μ (gradient f) x₀ nS) - f xstar ≤ ε ∧
        ((restartQueries cfg R μ (gradient f) x₀ nS).length : ℝ) ≤
          C * (Sε + min (Real.sqrt κ * Sε)
            (((χ : ℝ) * κ) ^ ((1 : ℝ) / 3) * Sε + ((χ : ℝ) * κ₂) ^ ((1 : ℝ) / 3))) ∧
        (∀ G' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          (∀ p ∈ restartQueries cfg R μ (gradient f) x₀ nS, gradient f p = G' p) →
            restartPt cfg R μ G' x₀ nS = restartPt cfg R μ (gradient f) x₀ nS) := by sorry

end RollingProbeQN.Convex.Supplement
