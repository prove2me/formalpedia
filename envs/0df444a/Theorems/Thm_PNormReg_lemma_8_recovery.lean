-- Prove2me | Theorems.Thm_PNormReg_lemma_8_recovery
-- name    : PNormReg.lemma_8_recovery
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:38.893209+00:00
-- url     : https://prove2.me/theorems/f4386090-dec7-42a1-b4f9-e10ebb2751b6
-- title:
--   Proof of Lemma 8, p.24 — the right scale exists among $O(\log p)$ values, and a duality-gap solution recovers $\mathrm{res}_p(\Delta_\zeta)\ge(\lambda_\xi/32)\mathrm{res}^\star_p$
-- statement:
--   Assume (16), $\nu/2<f(x)-f^\star\le\nu$, at a feasible $x$, with $\xi>1$, $Z$ as in (17), $A=NZ$, and $w$ Lewis weight overestimates of $A$. Then:
--
--   1. $\nu/(32p)<\phi^\star=\mathrm{res}^\star_p\le\nu$;
--   2. among the values $\zeta=\nu/2^j>\nu/(64p)$ of Algorithm 3, at least one satisfies $\phi^\star\in(\zeta/2,\zeta]$, and all have $j<\lceil\log_2(64p)\rceil$;
--   3. at a scale with $\phi^\star\in(\zeta/2,\zeta]$ and for $LL^\top=\bar D$: $\|L^{-1}\bar h\|_2^2\ge2/3$, the game (21) has optimum at most 1, and any pair with additive duality gap at most $\gamma=\min\{1/2,\xi-1\}$ has primal objective at most $1+\gamma\le\xi$, and its recovered $\tilde u$ is feasible for (19) with $\|\bar A\tilde u\|_p\le\xi$ and
--
--   $$\mathrm{res}_p(\lambda_\xi Z\tilde u)=\phi(\lambda_\xi\tilde u)\ge\frac{\lambda_\xi}{16}\phi^\star\ge\frac{\lambda_\xi}{32}\mathrm{res}^\star_p.$$
--
--   This is the correctness of one residual call: a logarithmic number of constant-accuracy games yields a constant-factor residual maximizer.
--
--   **Formalization Note** The time and failure-probability clauses of Lemma 8 are carried by Theorem 9.
--
--   Differences from the source:
--   - encoding: "An additive duality gap of min{1/2, ξ − 1}" → h(x̃, y) − h(x, ỹ) ≤ γ for all feasible x, y; reason: equivalent to max_y h(x̃, y) − min_x h(x, ỹ) ≤ γ on compact balls
--   - generalization: D̄^{−1/2} in the game and the recovery; C of full row rank → any L with LL⊤ = D̄ (printed root and Cholesky factor are both instances); any full column rank Z with image ker C; reason: the statement quantifies over a wider set that contains the printed choices
--   - encoding: Lemma 8 (with time and probability clauses) → the proof's display, not stated under Lemma 8's number; reason: the time clause is carried by PNormReg.theorem_9; the norm content is PNormReg.lemma_8_norms
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Proof of Lemma 8, scale and recovery, p.24 (PDF p.25); Algorithm 3, p.21; (16), p.21

import Mathlib
import Definitions.Def_PNormReg_Regression
import Definitions.Def_PNormReg_Scaled

open Matrix

namespace PNormReg

/-- **Proof of Lemma 8**, scale and recovery, p.24 (PDF p.25), with Algorithm 3, p.21.

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

Under (16), `ν/2 < f(x) − f⋆ ≤ ν`, with `ξ > 1`, `Z`, `A := NZ`, `h`, `D` as in (17), and overestimates `w`
of `A`:
* `ν/(32p) < φ⋆ = res⋆_p ≤ ν`;
* some value `ζ = ν/2^j` of Algorithm 3's loop (`ζ > ν/(64p)`) has `φ⋆ ∈ (ζ/2, ζ]`;
* each loop value has `j < K = ⌈log₂(64p)⌉`;
* at a scale with `φ⋆ ∈ (ζ/2, ζ]` and for any `L` with `LL⊤ = D̄`: `∥L^{−1}h̄∥₂² ≥ 2/3`, the game has optimum
  at most 1, and any pair with additive duality gap at most `min{1/2, ξ−1}` has primal objective at most
  `1 + min{1/2, ξ−1} ≤ ξ`, a recovered `ũ` feasible for (19) with `∥Āũ∥_p ≤ ξ`, and
  `res_p(λ_ξZũ) = φ(λ_ξũ) ≥ (λ_ξ/16)φ⋆ ≥ (λ_ξ/32)res⋆_p`.

**Formalization Note.** Lemma 8's time clause is carried by `PNormReg.theorem_9`. A duality gap at most
`γ` is written `h(x̃, y) − h(x, ỹ) ≤ γ` for all feasible `x, y`, which is `max_y h(x̃, y) − min_x h(x, ỹ) ≤ γ`. -/
theorem lemma_8_recovery {n d m k : ℕ} (G : GenRegression n d m) (hG : G.IsStanding) (p : ℝ)
    (hp : 2 ≤ p) (x : Fin d → ℝ) (hx : G.Feasible x) (ν ξ : ℝ)
    (hν₁ : ν / 2 < G.obj p x - G.fStar p) (hν₂ : G.obj p x - G.fStar p ≤ ν) (hξ : 1 < ξ)
    (Z : Matrix (Fin d) (Fin k) ℝ) (hZ : Function.Injective Z.mulVec)
    (hrange : ∀ Δ, G.C *ᵥ Δ = 0 ↔ ∃ u, Z *ᵥ u = Δ) (w : Fin n → ℝ)
    (hw : IsLewisOver (G.N * Z) (1 / p) w) :
    let A : Matrix (Fin n) (Fin k) ℝ := G.N * Z
    let h : Fin k → ℝ := Zᵀ *ᵥ G.grad p x
    let D : Matrix (Fin k) (Fin k) ℝ := Zᵀ * G.hess p x * Z
    let γ : ℝ := min (1 / 2) (ξ - 1)
    (ν / (32 * p) < phiStar h D A p ∧ phiStar h D A p = G.resStar p x ∧ G.resStar p x ≤ ν) ∧
    (∃ j : ℕ, ν / (64 * p) < ν / 2 ^ j ∧
      (ν / 2 ^ j) / 2 < phiStar h D A p ∧ phiStar h D A p ≤ ν / 2 ^ j) ∧
    (∀ j : ℕ, ν / (64 * p) < ν / 2 ^ j → j < ⌈Real.logb 2 (64 * p)⌉₊) ∧
    ∀ (ζ : ℝ), ζ / 2 < phiStar h D A p → phiStar h D A p ≤ ζ →
      ∀ L : Matrix (Fin k) (Fin k) ℝ, L * Lᵀ = scaledD A D h w p ζ →
        let hbar := scaledH h ζ
        let Abar := scaledA A p ζ
        let M := gameM Abar L hbar
        let c := gameC Abar L hbar
        2 / 3 ≤ l2Norm (L⁻¹ *ᵥ hbar) ^ 2 ∧
        (∃ x₁ : Fin k → ℝ, l2Norm x₁ ≤ 1 ∧ ∀ y : Fin n → ℝ, lpNorm (conjExp p) y ≤ 1 →
          gameObj M c x₁ y ≤ 1) ∧
        ∀ (xt : Fin k → ℝ) (yt : Fin n → ℝ), l2Norm xt ≤ 1 → lpNorm (conjExp p) yt ≤ 1 →
          (∀ (x₁ : Fin k → ℝ) (y : Fin n → ℝ), l2Norm x₁ ≤ 1 → lpNorm (conjExp p) y ≤ 1 →
            gameObj M c xt y - gameObj M c x₁ yt ≤ γ) →
          (∀ y : Fin n → ℝ, lpNorm (conjExp p) y ≤ 1 → gameObj M c xt y ≤ 1 + γ) ∧
          1 + γ ≤ ξ ∧
          scaledConstraint hbar (scaledD A D h w p ζ) (recover L hbar xt) ≤ -(1 / 8) ∧
          lpNorm p (Abar *ᵥ recover L hbar xt) ≤ ξ ∧
          G.res p x (lambdaXi p ξ • (Z *ᵥ recover L hbar xt)) =
            phi h D A p (lambdaXi p ξ • recover L hbar xt) ∧
          (lambdaXi p ξ / 16) * phiStar h D A p ≤
            phi h D A p (lambdaXi p ξ • recover L hbar xt) ∧
          (lambdaXi p ξ / 32) * G.resStar p x ≤ (lambdaXi p ξ / 16) * phiStar h D A p := by sorry

end PNormReg
