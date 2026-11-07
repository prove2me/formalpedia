-- Prove2me | Theorems.Thm_PolyEulerFlow_lemma_36
-- name    : PolyEulerFlow.lemma_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:03.139198+00:00
-- url     : https://prove2.me/theorems/3b3c5904-4ab6-4b4b-9a48-561964a095e5
-- title:
--   Lemma 36 — accumulation with an interval-product bound
-- statement:
--   With the constants of Lemma 31 and of Lemma 35 (in particular $B$ of (37)), and $r^*=r_0/(4D^*)$ with $D^*=\max(1,\max_\sigma\|D_\sigma\|_\infty)$, there is $s_0$ such that, for $s\ge s_0$, $h=2^{-s}$, $\varepsilon=h^K$ and $0\le\nu\le\varepsilon^2$: for a valid prefix $C_0,\dots,C_T$ of a separated affine program with interval gain bound $\Gamma\ge1$, if
--   $$B\Gamma T\Delta_\varepsilon\le r^*h,\tag{39}$$
--   then every execution of the compiled field from the prescribed initialization, for every mesh and every disturbance of level $\nu$, has its first $4T$ phase entries, each cycle of the prefix starts at a state admissible above its configuration, and
--   $$\|Y(t_{4k})-C_k\|_\infty\le B\Gamma k\Delta_\varepsilon\le r^*h\qquad(0\le k\le T).$$
--   Moreover, for every $G>0$ and every polynomial $T(s)$, $GBT(s)\Delta_\varepsilon/h^2\le r^*$ (40) for all sufficiently large $s$ and all $0\le\nu\le\varepsilon^2$, since $K/4>2$.
--
--   Errors are not multiplied through the cycles: the local defects are propagated by interval products, which is what allows exponentially long computations at unit step.
--
--   Differences from the source:
--   - generalization: every mesh 0 < η ≤ 1 (one constant step) → every variable mesh 0 < η_k ≤ 1 with Σ η_k = ∞; reason: Corollary 39 (p.34) states that every clock, cut and cycle estimate holds on such meshes; every constant step in (0, 1] is one of them
--   - reading: B the constant of Lemma 35 → B existential together with A, s₀, the box and C_cyc, jointly with the cycle property of Lemma 35; reason: the lemma refers to Lemma 35's constant
--   - reading: each cycle of this prefix is admissible → the cycles k < T start at states admissible above C_k; reason: the prefix has T cycles
--   - reading: the prefix executed from the initialization → the execution of the compiled field from the intended initial section of p.27; reason: Lemma 36 is applied to these executions in the proofs of Theorem 14 and Theorem 1
--   - generalization: for the stack normal form one can use Γ = G/h; for a polynomial T = T(s), (40) holds for large s whenever K/4 > 2 → for every G > 0 and every real polynomial T, (40) holds eventually in s; reason: the stack normal form's G (Lemma 25) is one such constant
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Lemma 36, pp.32–33 (PDF 34–35)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsCycleConstants

namespace PolyEulerFlow

/-- **Lemma 36 (Accumulation with an interval-product bound)**, pp.32–33 (PDF 34–35). Bournez, One Polynomial Field for Every Euler Step
and the Flow (manuscript, sha256 c4e01b2b…).

With the constants of Lemma 31 and of Lemma 35 (`B` the defect constant of (37)), and `r∗ = r₀/(4D∗)`, `D∗ = max(1, max_σ ‖D_σ‖∞)` (p.32): for a
valid prefix `C₀, …, C_T` of a separated affine program with interval gain bound `Γ ≥ 1`, if `BΓT∆ε ≤ r∗h` (39), then every execution of the compiled
field from the prescribed initialization (exact or perturbed) has its first `4T` phase entries, each cycle of the prefix starts at a state admissible
above its configuration, and `‖Y(t_{4k}) - C_k‖∞ ≤ BΓk∆ε ≤ r∗h` for `k ≤ T`. Moreover (the arithmetic of (40)): for every `G > 0` and every polynomial
`T(s)`, `GBT(s)∆ε/h² ≤ r∗` for all sufficiently large `s`, uniformly in `0 ≤ ν ≤ ε²`, since `K/4 > 2`.

**Formalization Note** The prescribed initialization is the intended initial section of p.27 (`initState`). The mesh is variable (Corollary 39,
p.34). The step "for the stack normal form one can use `Γ = G/h`" is Lemma 25; here the resulting condition (40) is stated for every `G > 0`. -/
theorem lemma_36 :
    ∃ A0 B0 Cdur Cenv Cnext Dclk ε0 : ℝ, IsUniformClock A0 B0 Cdur Cenv Cnext Dclk ε0 ∧
    ∀ (m g : ℕ) (prog : SeparatedAffineProgram m g) (K : ℕ), 256 ≤ K →
      ∃ (A B : ℝ) (s0 : ℕ) (lo hi : CompiledState m g) (Ccyc : ℝ), 0 < s0 ∧
        IsCycleConstants prog K A0 B0 A B s0 lo hi Ccyc ∧
        (∀ s : ℕ, s0 ≤ s →
          let h := scale s
          let ε := h ^ K
          ∀ (ν : ℝ) (C : ℕ → Fin m → ℝ) (T : ℕ) (Γ : ℝ), 0 ≤ ν → ν ≤ ε ^ 2 →
            prog.IsValidPrefix h C T → prog.IsGainBound h C T Γ →
            B * Γ * T * deltaEps ε ν ≤ prog.rStar * h →
            ∀ (η : ℕ → ℝ) (ξ : ℕ → CompiledState m g), IsAdmissibleMesh η → IsPermittedDisturbance ν ξ →
              let z := eulerOrbit (compiledField prog K h) (initState prog K h (C 0)) η ξ
              ∃ kk : ℕ → ℕ, IsPhaseEntriesUpTo phaseBit z 0 (4 * T) kk ∧
                (∀ k < T, IsAdmissibleAbove prog K A0 B0 A ν h (C k) (z (kk (4 * k)))) ∧
                (∀ k ≤ T, ‖dataY (z (kk (4 * k))) - C k‖ ≤ B * Γ * k * deltaEps ε ν ∧
                  B * Γ * k * deltaEps ε ν ≤ prog.rStar * h)) ∧
        (∀ (G : ℝ) (Tpoly : Polynomial ℝ), 0 < G →
          ∀ᶠ s : ℕ in Filter.atTop, ∀ ν : ℝ, 0 ≤ ν → ν ≤ (scale s ^ K) ^ 2 →
            G * B * Tpoly.eval (s : ℝ) * deltaEps (scale s ^ K) ν / scale s ^ 2 ≤ prog.rStar) := by sorry

end PolyEulerFlow
