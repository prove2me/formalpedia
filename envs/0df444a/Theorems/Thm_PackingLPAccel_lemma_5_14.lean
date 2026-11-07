-- Prove2me | Theorems.Thm_PackingLPAccel_lemma_5_14
-- name    : PackingLPAccel.lemma_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:38.117022+00:00
-- url     : https://prove2.me/theorems/452fd4d8-ae43-4b3e-beee-7582087b6c59
-- title:
--   Lemma 5.14 — iterative refinement for composite $\ell_{q,p}$-regression (corrected: residual $c_{ij}$ and error $\alpha\omega\delta$)
-- statement:
--   Let $\mathcal X_j\subset\mathbb R^m_{\ge0}$ be nonempty, convex and compact with $\psi_j$ convex, and let $\lambda>0$, $p\ge2$, $q=1+1/p$, $\omega=4096p^4$. Write $\mathcal E=\mathcal E^\lambda_{q,p}$ and let $\mathcal F$ be the corrected residual. For feasible $X$ and $X+\Delta$,
--
--   $$\omega\mathcal F(\Delta/\omega;X)\le\mathcal E(X+\Delta)-\mathcal E(X)\le\mathcal F(\Delta;X).$$
--
--   Let $\alpha\ge1$, $\delta\ge0$, and let $X_0,\dots,X_T$ be feasible with $\mathcal F(X_{t+1}-X_t;X_t)\le\alpha^{-1}\mathcal F(\Delta';X_t)+\delta$ for all feasible $\Delta'$. Then, for every minimizer $X^\star$,
--
--   $$\mathcal E(X_T)-\mathcal E(X^\star)\le\Bigl(1-\frac1{\alpha\omega}\Bigr)^T\bigl(\mathcal E(X_0)-\mathcal E(X^\star)\bigr)+\alpha\omega\delta.$$
--
--   If moreover $\mathcal X_j\subseteq[0,R]^m$, $|\psi|\le R_\psi$ on the feasible set, $\delta>0$, and $T\ge\alpha\omega\log\bigl((2R_\psi+\lambda m(kR^q)^p)/(\alpha\omega\delta)\bigr)$, then $\mathcal E(X_T)-\mathcal E(X^\star)\le2\alpha\omega\delta$.
--
--   A caller obtains the printed additive error $3\delta$ by asking the solver for accuracy $\delta/(\alpha\omega)$. When $R,R_\psi,\delta^{-1},\lambda=\exp(\widetilde O(1))$ and $p=O(\log m)$, the number of steps is $\widetilde O(\alpha)$.
--
--   Differences from the source:
--   - correction: c_ij(t) = λp q_i^{p−1}[(X_ij+|t|)^q − X_ij^q], v^{(2)}_i = λp²q_i^{p−2}, F(∆/ω;X) in (18) → c_ij(t) = λp q_i^{p−1}[|X_ij+t|^q − X_ij^q], v^{(2)}_i = 2λp²q_i^{p−2}, F(∆;X); reason: on E(x) = x⁴ (k = m = 1, X = [0,1], ψ = 0, λ = 1, p = 3) the printed residual is ≥ 0 = F(0), so ∆ = 0 is exact at every x and the iteration stays at gap 1/16; (41) fails at x = 1/2, ∆ = −0.01
--   - correction: additive error δ/(1 − 1/(αω)) in (42), 3δ in the lemma → αωδ in the recursion, 2αωδ after enough steps; reason: with α = 4, δ = 1/64, x₀ = 1/2 on E(x) = x⁴, ∆̂ = 0 is a valid (α,δ) answer at gap 4δ > 3δ; iterating (43) sums to αωδ
--   - reading: (α,δ) multiplicative-additive approximation → F(∆̂) ≤ (1/α)F(∆') + δ for all feasible ∆', with α ≥ 1; reason: the form the proofs use (p.41), not f(x̂) ≤ α OPT + β of p.7
--   - reading: in time Õ(α·T_α(m,k)) → an explicit number of steps T, each one call of the residual solver; reason: the time is T calls; the hypotheses on R, R_ψ, δ⁻¹, λ, p bound the logarithm
--   - generalization: p ∈ ℤ odd with p = O(log m), R, R_ψ, δ⁻¹, λ = exp(Õ(1)) → p real, p ≥ 2; R, R_ψ, δ, λ free; reason: these conditions are used only to read T = Õ(α) off the explicit bound
--   - reading: 1 < q ≤ 2 ≤ p → q = 1 + 1/p, p ≥ 2; reason: the standing assumption of §5.2 (p.23, "when p = Θ(log mn) and q = 1+1/p"); the residual (17)–(22) and ω = 4096p⁴ come from Lemma 5.13, which assumes it
--   - generalization: the lemma states only the algorithm's guarantee → the sandwich (41) is an extra clause (a) of the conclusion; reason: a step of the proof (p.40) on which the guarantee rests; clauses (b), (c) carry the printed guarantee
--   - encoding: X_j ⊆ ℝ^m in Problem 5.1 → X_j ⊆ ℝ^m_{≥0}; reason: Definition 3.2 of a fine-grained instance
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Lemma 5.14, p.25 (pdf 26); proof pp.40–41 (pdf 41–42), displays (41)–(43)

import Mathlib
import Definitions.Def_PackingLPAccel_Proxy

namespace PackingLPAccel

/-- **Lemma 5.14, corrected** (manuscript sha256 1dac7711…, p.25; proof pp.40–41). Part (a) is (41) for the corrected
residual; (b) is the corrected form of (42): the additive term is `αωδ`, not `δ / (1 - 1/(αω))`; (c) is the time
clause as an iteration count, each step being one call of the residual solver. `p` need not be an odd integer.
A caller gets the printed `3δ` by asking the solver for accuracy `δ / (αω)`. -/
theorem lemma_5_14 {m k : ℕ} (I : CompositeInstance m k) (_ : I.IsValid)
    (lam p q : ℝ) (_ : 0 < lam) (_ : 2 ≤ p) (_ : q = 1 + 1 / p) :
    (∀ X Δ : Matrix (Fin m) (Fin k) ℝ, I.Mem X → I.Mem (X + Δ) →
      4096 * p ^ 4 * correctedF I lam p q X ((4096 * p ^ 4)⁻¹ • Δ) ≤
          qpEnergy I lam p q (X + Δ) - qpEnergy I lam p q X ∧
        qpEnergy I lam p q (X + Δ) - qpEnergy I lam p q X ≤ correctedF I lam p q X Δ) ∧
    ∀ (α δ : ℝ) (_ : 1 ≤ α) (_ : 0 ≤ δ) (X : ℕ → Matrix (Fin m) (Fin k) ℝ) (T : ℕ)
      (_ : ∀ t ≤ T, I.Mem (X t))
      (_ : ∀ t < T, ∀ Δ' : Matrix (Fin m) (Fin k) ℝ, I.Mem (X t + Δ') →
        correctedF I lam p q (X t) (X (t + 1) - X t) ≤
          α⁻¹ * correctedF I lam p q (X t) Δ' + δ)
      (Xs : Matrix (Fin m) (Fin k) ℝ) (_ : I.Mem Xs)
      (_ : ∀ Y, I.Mem Y → qpEnergy I lam p q Xs ≤ qpEnergy I lam p q Y),
      qpEnergy I lam p q (X T) - qpEnergy I lam p q Xs ≤
          (1 - (α * (4096 * p ^ 4))⁻¹) ^ T *
            (qpEnergy I lam p q (X 0) - qpEnergy I lam p q Xs) + α * (4096 * p ^ 4) * δ ∧
      ∀ (R Rψ : ℝ) (_ : 0 ≤ R) (_ : ∀ j, ∀ y ∈ I.X j, ∀ i, y i ≤ R)
        (_ : ∀ Y, I.Mem Y → |I.psi Y| ≤ Rψ) (_ : 0 < δ)
        (_ : α * (4096 * p ^ 4) *
            Real.log ((2 * Rψ + lam * m * (k * R ^ q) ^ p) / (α * (4096 * p ^ 4) * δ)) ≤ T),
        qpEnergy I lam p q (X T) - qpEnergy I lam p q Xs ≤ 2 * (α * (4096 * p ^ 4) * δ) := by sorry

end PackingLPAccel
