-- Prove2me | Theorems.Thm_RegMT_Regress_theorem_3_1_ii
-- name    : RegMT.Regress.theorem_3_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:34.692143+00:00
-- url     : https://prove2.me/theorems/e6c10c75-7d1d-4e5c-bac7-1c320709958a
-- title:
--   Theorem 3.1(ii), p. 8 — Wasserstein-robust linear regression equals (1/N)Σ L(⟨w, x̂_i⟩ − ŷ_i) + ρ lip(L)‖(w, −1)‖_*
-- statement:
--   **Distributionally robust linear regression (Theorem 3.1(ii)).** Let the input-output space $\mathbb R^{n+1}$ carry an arbitrary norm $\|\cdot\|$, with dual norm $\|\cdot\|_*$, and let the transport cost be $d(\xi,\xi')=\|\xi-\xi'\|$ on $\Xi=\mathbb R^{n+1}$. Let $(\hat x_i,\hat y_i)\in\mathbb R^n\times\mathbb R$, $i=1,\dots,N$ with $N\ge1$, be training samples with empirical distribution $\hat{\mathbb P}_N$. For $\rho\ge0$, let $\mathbb B_\rho(\hat{\mathbb P}_N)$ be the type-1 Wasserstein ball (3) of radius $\rho$ around $\hat{\mathbb P}_N$. Let $L:\mathbb R\to\mathbb R$ be a nonnegative, convex, Lipschitz continuous loss function with Lipschitz modulus $\mathrm{lip}(L)$. The regression loss of the weight vector $w\in\mathbb R^n$ is $\ell_w(x,y)=L(\langle w,x\rangle-y)$.
--
--   Then the distributionally robust regression problem (4) is equivalent to the regularized problem (6), in the following sense.
--
--   1. For every $w\in\mathbb R^n$,
--   $$
--   \sup_{\mathbb Q\in\mathbb B_\rho(\hat{\mathbb P}_N)}\mathbb E^{\mathbb Q}\big[L(\langle w,x\rangle-y)\big]
--   \;=\;\frac1N\sum_{i=1}^N L(\langle w,\hat x_i\rangle-\hat y_i)\;+\;\rho\,\mathrm{lip}(L)\,\|(w,-1)\|_* .
--   $$
--   2. Consequently, the optimal values agree:
--   $$
--   \inf_{w}\ \sup_{\mathbb Q\in\mathbb B_\rho(\hat{\mathbb P}_N)}\mathbb E^{\mathbb Q}\big[L(\langle w,x\rangle-y)\big]
--   \;=\;\inf_w\ \frac1N\sum_{i=1}^N L(\langle w,\hat x_i\rangle-\hat y_i)+\rho\,\mathrm{lip}(L)\,\|(w,-1)\|_* .
--   $$
--
--   The theorem shows that Wasserstein distributionally robust linear regression with a norm transport cost is empirical loss minimization with a dual-norm penalty. The penalty acts on the extended vector $(w,-1)$, because the transport cost moves outputs as well as inputs, and it is weighted by the radius and by the Lipschitz modulus of the univariate loss. For the Huber, $\epsilon$-insensitive and pinball losses this gives explicit regularized programs (Corollaries 3.2–3.4).
--
--   **Formalization Note.** $\mathbb R^{n+1}$ is an abstract finite-dimensional real normed space $E$ with Borel σ-algebra and a continuous linear isomorphism $e:E\to\mathbb R^n\times\mathbb R$ that reads off inputs and outputs, so the theorem covers every norm on $\mathbb R^{n+1}$. The worst case is the published `worstCaseRisk` with $p=1$, $\Xi=E$ and $\hat{\mathbb P}_N$ the published `empiricalDistribution`. Its expectations follow the extended-real convention of `nominalRisk`, and both sides live in the extended reals. $\|(w,-1)\|_*$ is the operator norm of `pairing e w`, and $\mathrm{lip}(L)$ is the published `lipschitzModulus` of the univariate $L$, valued in $[0,\infty]$ and finite here. The paper does not define "equivalent". The statement is the per-$w$ identity that the proof establishes (pp. 30–31) together with the equality of optimal values, which follows from it. No attainment of the infimum is claimed. The radius $\rho=0$ is included, in which case both sides reduce to the empirical loss. The standing assumption $L\ge0$ of §2.1 is included.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 8, Theorem 3.1(ii), (6); setting §3.1 preamble p. 8, (3)–(4) p. 7; proof pp. 30–31

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk_v2
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus
import Definitions.Def_RegMT_Regress_Model

open WassersteinDRO.Duality

namespace RegMT.Regress

/-- Theorem 3.1(ii) (Distributionally robust linear regression), Shafieezadeh-Abadeh, Kuhn &
Mohajerin Esfahani, *Regularization via Mass Transportation*, arXiv:1710.10016v3, p. 8, (6).

Setting (§3.1, p. 8): the input-output space `ℝ^{n+1}` carries an arbitrary norm and is modelled
as `E` with input/output coordinates `e : E ≃L[ℝ] ℝⁿ × ℝ`; the transport cost is `‖ξ − ξ'‖` and
`Ξ = E`; `L : ℝ → ℝ` is nonnegative, convex and Lipschitz continuous; the samples are `(xhat i, yhat i)`,
`i < N`, `N ≥ 1`; `ρ ≥ 0` is the radius of the Wasserstein ball (3) around the empirical
distribution `P̂_N`. The worst case `sup_{Q ∈ B_ρ(P̂_N)} E^Q[L(⟨w, x⟩ − y)]` of (4) is
`worstCaseRisk ρ 1 Set.univ P̂_N (L ∘ pairing e w)`.

Conclusion ("(4) is equivalent to (6)"): (1) for every `w` the worst-case expected loss equals the
objective of (6), `(1/N) Σᵢ L(⟨w, xhat i⟩ − yhat i) + ρ · lip(L) · ‖(w, −1)‖_*`, with `lip(L)` the
Lipschitz modulus of `L` and `‖(w, −1)‖_*` the operator norm of `pairing e w`; (2) consequently the
optimal values of (4) and (6) agree. -/
theorem theorem_3_1_ii {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n N : ℕ}
    (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hN : 0 < N)
    (xhat : Fin N → Fin n → ℝ) (yhat : Fin N → ℝ)
    (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L) (h_nonneg : ∀ z, 0 ≤ L z)
    (hLip : ∃ K, LipschitzWith K L) :
    (∀ w : Fin n → ℝ,
      worstCaseRisk ρ 1 Set.univ (empiricalDistribution fun i => e.symm (xhat i, yhat i))
          (fun ξ => L (pairing e w ξ)) =
        (((N : ℝ)⁻¹ * ∑ i, L (∑ j, w j * xhat i j - yhat i) : ℝ) : EReal) +
          ((ENNReal.ofReal ρ * lipschitzModulus L * ENNReal.ofReal ‖pairing e w‖ : ENNReal) :
            EReal)) ∧
    (⨅ w : Fin n → ℝ,
      worstCaseRisk ρ 1 Set.univ (empiricalDistribution fun i => e.symm (xhat i, yhat i))
          (fun ξ => L (pairing e w ξ))) =
      ⨅ w : Fin n → ℝ,
        (((N : ℝ)⁻¹ * ∑ i, L (∑ j, w j * xhat i j - yhat i) : ℝ) : EReal) +
          ((ENNReal.ofReal ρ * lipschitzModulus L * ENNReal.ofReal ‖pairing e w‖ : ENNReal) :
            EReal) := by sorry

end RegMT.Regress
