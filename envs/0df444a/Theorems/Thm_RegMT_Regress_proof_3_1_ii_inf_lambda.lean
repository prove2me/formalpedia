-- Prove2me | Theorems.Thm_RegMT_Regress_proof_3_1_ii_inf_lambda
-- name    : RegMT.Regress.proof_3_1_ii_inf_lambda
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:41.123474+00:00
-- url     : https://prove2.me/theorems/8e54d1c8-890a-4669-b293-c75ec47b22b7
-- title:
--   Proof of Theorem 3.1(ii), p. 30 — worst-case loss = inf{λρ + (1/N)Σ L(⟨w, x̂_i⟩ − ŷ_i) : lip(L)‖(w, −1)‖_* ≤ λ}
-- statement:
--   Let the input-output space $\mathbb R^{n+1}$ carry an arbitrary norm $\|\cdot\|$, with dual norm $\|\cdot\|_*$. Let $(\hat x_i,\hat y_i)\in\mathbb R^n\times\mathbb R$, $i=1,\dots,N$ with $N\ge1$, be training samples with empirical distribution $\hat{\mathbb P}_N=\frac1N\sum_{i=1}^N\delta_{(\hat x_i,\hat y_i)}$. For $\rho\ge0$, let $\mathbb B_\rho(\hat{\mathbb P}_N)$ be the set of probability distributions $\mathbb Q$ on $\mathbb R^{n+1}$ whose type-1 Wasserstein distance from $\hat{\mathbb P}_N$, with transport cost $\|\xi-\xi'\|$, is at most $\rho$. Let $L:\mathbb R\to\mathbb R$ be nonnegative, convex and Lipschitz continuous with Lipschitz modulus $\mathrm{lip}(L)$. Then for every fixed $w\in\mathbb R^n$
--
--   $$
--   \sup_{\mathbb Q\in\mathbb B_\rho(\hat{\mathbb P}_N)}\mathbb E^{\mathbb Q}\big[L(\langle w,x\rangle-y)\big]
--   \;=\;
--   \inf\Big\{\lambda\rho+\frac1N\sum_{i=1}^N L(\langle w,\hat x_i\rangle-\hat y_i)\;:\;\lambda\ge0,\ \mathrm{lip}(L)\,\|(w,-1)\|_*\le\lambda\Big\}.
--   $$
--
--   This is the intermediate identity of the proof of Theorem 3.1(ii). It is the dual reformulation of Lemma A.1 with every inner supremum evaluated by Lemma A.3. Eliminating $\lambda$ gives the closed form in Theorem 3.1(ii).
--
--   The printed display (p. 30) omits the factor $\frac1N$ in front of the sum in its first line and has a stray factor $|\theta|$ in the constraint ("$\mathrm{lip}(L)|\theta|\cdot\|(w,-1)\|_*\le\lambda$"). The statement here has the factor $\frac1N$ and no $|\theta|$, which is what Lemma A.1 and Lemma A.3 give.
--
--   **Formalization Note.** $\mathbb R^{n+1}$ is an abstract finite-dimensional real normed space $E$ with Borel σ-algebra and coordinates $e:E\to\mathbb R^n\times\mathbb R$. The worst case is the published `worstCaseRisk` with $p=1$ and $\Xi=E$. Its expectations use the extended-real convention of the published `nominalRisk`, and both sides are extended reals. $\|(w,-1)\|_*$ is the operator norm of `pairing e w`. $\mathrm{lip}(L)\in[0,\infty]$ is compared in $[0,\infty]$, and the explicit $\lambda\ge0$ (the range of the dual variable in Lemma A.1) makes that comparison the real constraint $\mathrm{lip}(L)\|(w,-1)\|_*\le\lambda$. The radius $\rho=0$ is included. There the ball is $\{\hat{\mathbb P}_N\}$ and both sides equal the empirical loss. The proof route through Lemma A.1 needs $\rho>0$, so $\rho=0$ is a separate case for the solver. The standing assumption $L\ge0$ of §2.1 is included.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, pp. 30–31, proof of Theorem 3.1, assertion (ii) (display after "Thus we find", corrected: factor 1/N, no |θ|)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk_v2
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus
import Definitions.Def_RegMT_Regress_Model

open WassersteinDRO.Duality

namespace RegMT.Regress

/-- Proof of Theorem 3.1(ii), Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, *Regularization via
Mass Transportation*, arXiv:1710.10016v3, pp. 30–31 (the display after "Thus we find", corrected):
for a fixed weight vector `w`, the worst-case expected regression loss over the type-1 Wasserstein
ball of radius `ρ ≥ 0` around the empirical distribution of the samples `(xhat i, yhat i)` equals
`inf {λρ + (1/N) Σᵢ L(⟨w, xhat i⟩ − yhat i) : λ ≥ 0, lip(L)‖(w, −1)‖_* ≤ λ}`.

Setting (§3.1, p. 8): the input-output space `ℝ^{n+1}` is `E` with an arbitrary norm, coordinates
`e`, transport cost `‖ξ − ξ'‖`, `Ξ = E`; `L` is nonnegative, convex and Lipschitz continuous;
`(w, −1)` is the functional `pairing e w` and its dual norm is the operator norm. The printed
display omits the factor `1/N` in its first line and carries a stray `|θ|` in the constraint;
both are corrected here. `λ ≥ 0` is the range of the dual variable of Lemma A.1 and is implied by
the constraint in the reals. -/
theorem proof_3_1_ii_inf_lambda {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n N : ℕ}
    (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hN : 0 < N)
    (xhat : Fin N → Fin n → ℝ) (yhat : Fin N → ℝ)
    (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L) (h_nonneg : ∀ z, 0 ≤ L z)
    (hLip : ∃ K, LipschitzWith K L)
    (w : Fin n → ℝ) :
    worstCaseRisk ρ 1 Set.univ (empiricalDistribution fun i => e.symm (xhat i, yhat i))
        (fun ξ => L (pairing e w ξ)) =
      ⨅ (lam : ℝ) (_ : 0 ≤ lam)
        (_ : lipschitzModulus L * ENNReal.ofReal ‖pairing e w‖ ≤ ENNReal.ofReal lam),
        ((lam * ρ + (N : ℝ)⁻¹ * ∑ i, L (∑ j, w j * xhat i j - yhat i) : ℝ) : EReal) := by sorry

end RegMT.Regress
