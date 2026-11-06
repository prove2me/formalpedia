-- Prove2me | Theorems.Thm_RankOneSK_lemma_4_1
-- name    : RankOneSK.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:45.213015+00:00
-- url     : https://prove2.me/theorems/d8b1aeda-62e4-4cc6-bd47-2f533d8f1863
-- title:
--   Lemma 4.1 — explicit description of $A$: $A=\mathrm{diag}(J,J,1)(A_0+E)\mathrm{diag}(J,J,1)$ with $\|E\|_{\mathrm{op}}=O(|J|)$
-- statement:
--   Let $\mu_{J,a,b}$ be the two-spin Ising measure with raw interaction $J$, $\bar X_0=\tanh a$, $\bar Y_0=\tanh b$, $\sigma_{X_0}=\sqrt{1-\bar X_0^2}$, $\sigma_{Y_0}=\sqrt{1-\bar Y_0^2}$, and $\varphi(X),\varphi(Y)$ the normalized spins. For parameters $d,s,\lambda$ let $Q(f)$ be the right-hand side of (36):
--   $$Q(f)=\mathbb E[(L_Xf)(L_Yf)]+J\,\mathbb E[M(L_Xf)(L_Yf)]+\tfrac{(\lambda J)^2}2\mathbb E[(L_Xf)^2+(L_Yf)^2]+\tfrac{dJ^2}2\mathbb E[\bar X(y)^2(L_Xf)^2+\bar Y(x)^2(L_Yf)^2].$$
--
--   **Lemma 4.1.** For all $d,s,\lambda\in\mathbb R$ there is a constant $K=K(d,s,\lambda)$ such that the following holds for all $a,b\in\mathbb R$ and $|J|\le\tfrac12$. Let $A\in\mathbb R^{3\times3}$ be the symmetric matrix with $[\alpha\ \beta\ \gamma]\,A\,[\alpha\ \beta\ \gamma]^\top=Q(f)$ for every $f=f_0+\alpha\varphi(x)+\beta\varphi(y)+\gamma\varphi(x)\varphi(y)$. Then
--   $$A=\mathrm{diag}(J,J,1)\,(A_0+E)\,\mathrm{diag}(J,J,1),\qquad\|E\|_{\mathrm{op}}\le K|J|,$$
--   where
--   $$A_0=\begin{pmatrix}\tfrac12(\lambda^2+d\bar X_0^2)&-\tfrac12(s^2+2s-1)\bar X_0\bar Y_0\sigma_{X_0}\sigma_{Y_0}&-\tfrac12(1-s)\bar X_0\sigma_{Y_0}\\-\tfrac12(s^2+2s-1)\bar X_0\bar Y_0\sigma_{X_0}\sigma_{Y_0}&\tfrac12(\lambda^2+d\bar Y_0^2)&-\tfrac12(1-s)\bar Y_0\sigma_{X_0}\\-\tfrac12(1-s)\bar X_0\sigma_{Y_0}&-\tfrac12(1-s)\bar Y_0\sigma_{X_0}&1\end{pmatrix}.$$
--
--   Since $A_0\succeq cI$ for $d,s,\lambda$ as in Theorem 3.1, the lemma reduces the local inequality to a perturbation bound. Here $\alpha,\beta,\gamma$ are coefficients, not the temperature.
--
--   Differences from the source:
--   - generalization: d, s, λ those of Theorem 3.1 (d, s ⩽ 1, λ > 0, (24)), the context in which the lemma is used → any real d, s, λ, with K depending on (d, s, λ); reason: the lemma states no restriction on d, s, λ and its O(|J|) constant may depend on them; restricting to Theorem 3.1 parameters gives the source
--   - encoding: "Let A be the unique symmetric matrix such that (36)" → for every symmetric A satisfying (36) for all f₀, α, β, γ; reason: exactly one such A exists, so the statements agree
--   - encoding: ∥E∥_op ⩽ O(|J|) → ∃ E with A = D(A₀ + E)D and ℓ²-operator norm of E (LiqPremiaEq.opNorm) ⩽ K|J|, K chosen before a, b, J; reason: meaning of O(·); the constant may depend on d, s, λ
--   - encoding: x, y ∈ {±1}; expectations under µ_{J,a,b} → Bool spins read as ±1; twoSpinExp J a b; reason: Lean convention; same objects
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 4.1 and (36), p.24 (PDF p.25)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_localForm
import Definitions.Def_RankOneSK_phi
import Definitions.Def_LiqPremiaEq_opNorm

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Lemma 4.1 (Explicit description of A).** Let `A ∈ ℝ^{3×3}` be the symmetric matrix such that for
every `f₀, α, β, γ ∈ ℝ` and `f = f₀ + αφ(x) + βφ(y) + γφ(x)φ(y)`, `[α β γ] A [α β γ]ᵀ` equals the
right-hand side of (36). Suppose also that `|J| ⩽ 1/2`. Then `A = diag(J, J, 1)(A₀ + E) diag(J, J, 1)`
where `∥E∥_op ⩽ O(|J|)` and `A₀` is the explicit matrix below.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Lemma 4.1 and display (36), p.24.

**Formalization Note** Two-spin objects: spins are `Bool` read as ±1 by `spinValue`; `twoSpinExp J a b` is
`E_{µ_{J,a,b}}` and `twoSpinExp 0 a b` is `E_{µ_{0,a,b}}`. `J` is the raw interaction (not `tanh J`), in `diag(J, J, 1)`,
in (36) and in `|J| ⩽ 1/2`. The right-hand side of (36) is `localForm d s lam J a b f`. The coefficients
`α, β, γ` are written `α β γ`; `β` here is not a temperature. The O(·) constant `K` may depend on the
parameters `d, s, λ` (as `λ²` and `d` multiply entries of `A₀`) and is chosen before `a, b, J, A`; the
lemma states no restriction on `d, s, λ`, so none is imposed. The statement is made for every symmetric
`A` satisfying (36) (there is exactly one). `∥·∥_op` is the `ℓ²` operator norm (the published `LiqPremiaEq.opNorm`). `X̄₀ = tanh a`,
`Ȳ₀ = tanh b`, `σ_{X₀} = √(1 − X̄₀²)`, `σ_{Y₀} = √(1 − Ȳ₀²)`. -/
theorem lemma_4_1 :
    ∀ d s lam : ℝ, ∃ K : ℝ, ∀ a b J : ℝ, |J| ≤ 1 / 2 →
      ∀ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm →
      (∀ f0 α β γ : ℝ,
        dotProduct ![α, β, γ] (A.mulVec ![α, β, γ]) =
          localForm d s lam J a b
            (fun x y => f0 + α * phi a x + β * phi b y + γ * (phi a x * phi b y))) →
      let X0 := Real.tanh a
      let Y0 := Real.tanh b
      let σX := Real.sqrt (1 - X0 ^ 2)
      let σY := Real.sqrt (1 - Y0 ^ 2)
      let A0 : Matrix (Fin 3) (Fin 3) ℝ :=
        !![1 / 2 * (lam ^ 2 + d * X0 ^ 2), -(1 / 2) * (s ^ 2 + 2 * s - 1) * X0 * Y0 * σX * σY,
            -(1 / 2) * (1 - s) * X0 * σY;
          -(1 / 2) * (s ^ 2 + 2 * s - 1) * X0 * Y0 * σX * σY, 1 / 2 * (lam ^ 2 + d * Y0 ^ 2),
            -(1 / 2) * (1 - s) * Y0 * σX;
          -(1 / 2) * (1 - s) * X0 * σY, -(1 / 2) * (1 - s) * Y0 * σX, 1]
      ∃ E : Matrix (Fin 3) (Fin 3) ℝ,
        A = Matrix.diagonal ![J, J, 1] * (A0 + E) * Matrix.diagonal ![J, J, 1] ∧
          LiqPremiaEq.opNorm E ≤ K * |J| := by sorry

end RankOneSK
