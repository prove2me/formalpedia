-- Prove2me | Theorems.Thm_SparseBatchBandit_theorem_2
-- name    : SparseBatchBandit.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:34:49.857841+00:00
-- url     : https://prove2.me/theorems/84baaaa0-1b60-40d5-b886-9061198c1517
-- title:
--   Theorem 2 — LBGL has regret $C M^{3/2}\sqrt{\log K\log(KT)\log(dT)}\,\sqrt{Ts_0}(T/s_0)^{1/(2(2^M-1))}/(\gamma\rho)$
-- statement:
--   Consider LASSO Batch Greedy Learning (Algorithm 1) under Model-C, Assumptions 1–4 and $M=O(\log\log(T/s_0))$. Then
--
--   $$
--   \sup_{\theta^\star:\ \|\theta^\star\|_2\le1,\ \|\theta^\star\|_0\le s_0}\mathbb E_{\theta^\star}[R_T]\le\frac{C\,M^{3/2}\sqrt{\log K\log(KT)\log(dT)}}{\gamma\rho}\cdot\sqrt{Ts_0}\cdot\Big(\frac{T}{s_0}\Big)^{\frac{1}{2(2^M-1)}},
--   $$
--
--   where $C>0$ is independent of $(T,d,M,K,s_0)$.
--
--   The result says that an exploration-free algorithm on a static grid, with $O(\log\log(T/s_0))$ batches, already matches the fully online regret $\tilde O(\sqrt{Ts_0})$ up to logarithmic factors.
--
--   **Formalization Note** The implied constants of the hypotheses are $A,\varepsilon,\beta,p$, and $C$ depends only on them. The result holds for every measurable selection of Lasso minimizers.
--
--   Differences from the source:
--   - reading: Assumption 1's display, at unit v only → HasSubgaussianMGF of ⟨v, x⟩ with proxy 1, for every λ and unit v; reason: the unit-scale bound is not sub-Gaussianity; §2.1 and p.18 use every scale
--   - reading: O, Ω and Poly with numerical constants → ∀ A ε β p, ∃ constants, ∀ instance; reason: the implied constants of the hypotheses are the only reading under which a bound can hold: a constant uniform over them would allow d = exp(T)
--   - reading: b = Θ(√T (T/s₀)^(1/(2(2^M−1)))), t₁ = b√s₀, t_m = ⌊b√t_{m−1}⌋, t_M = T → exact b, floors on every t_m, each capped at T, last point T; reason: the page leaves b open up to Θ, and a grid point is a round; this b makes the unrounded recursion end exactly at T
--   - reading: each batch is partitioned into M intervals evenly → q-th round in T_m^(j) iff ⌊(j−1)n/M⌋ < q ≤ ⌊jn/M⌋; reason: the page gives no formula; this is the even floor partition
--   - reading: no statement on the joint law of contexts and noises → the context family is independent of the noise family; reason: the proof on p.28 conditions on the selected contexts and uses this
--   - reading: a* = argmax without a tie-break in Assumption 2 → lowest-index maximizer, the rule of Algorithm 1; reason: the proof applies Assumption 2 at θ̂₀ = 0, where all arms tie
--   - generalization: θ̂_m is the argmin → θ̂_m is the output of an arbitrary measurable selection of minimizers; reason: the argmin need not be unique; the statement covers every choice, so it specializes to any rule the paper could mean
--   - generalization: M = O(log log(T/s₀)) → M ≤ A max(1, log log(T/s₀)); reason: keeps the small instances with log log(T/s₀) ≤ 1; large instances are the paper's
--   - encoding: no explicit ranges → T ≥ 2, d ≥ 1, K ≥ 2, M ≥ 1, s₀ ≥ 1, γ, ρ > 0; reason: the formulas degenerate outside them: K = 1 gives log K = 0 and T = 1, d = 1 makes the right side 0
--   - encoding: vectors in ℝ^d, rounds 1..T → Fin d → ℝ with the published l2Norm; rounds Fin T, round t + 1 of the page being t; reason: Lean convention; same instances
--   - encoding: sup over ‖θ⋆‖₂ ≤ 1, ‖θ⋆‖₀ ≤ s₀ → ∀ θstar with those bounds; reason: a bound on a supremum is a bound at each point
--   - encoding: the expectation E[R_T] → Integrable and the Bochner integral; reason: a Bochner integral of a non-integrable function is 0, so integrability is stated; the regret is integrable, being dominated by 2∑_t max_a|x_{t,a}⊤θ⋆|
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Theorem 2, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_Standing
import Definitions.Def_SparseBatchBandit_action
import Definitions.Def_SparseBatchBandit_regret
import Definitions.Def_SparseBatchBandit_regretRate
open MeasureTheory

namespace SparseBatchBandit

/-- **Theorem 2**, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, p.16 (PDF 16). Under Model-C, Assumptions 1–4 and `M = O(log log(T/s₀))`,
`sup_{θ⋆ : ‖θ⋆‖₂ ≤ 1, ‖θ⋆‖₀ ≤ s₀} E_{θ⋆}[R_T(Alg)] ≤
C · M^{3/2} √(log K log(KT) log(dT)) / (γρ) · √(Ts₀) · (T/s₀)^{1/(2(2^M−1))}`, where `Alg` is LBGL
and `C > 0` is a numerical constant independent of `(T, d, M, K, s₀)`.

**Formalization Note.** The implied constants of the hypotheses are `A, ε, β, p`, and `C` depends
only on them: it is chosen before every object of the instance. The `sup` is the `∀ θstar`. The
result holds for every measurable selection `sel` of Lasso minimizers. `Integrable` is part of the
conclusion because a Bochner integral of a non-integrable function is `0`. -/
theorem theorem_2 (A ε β : ℝ) (p : ℕ) (_hA : 0 < A) (_hε : 0 < ε) (_hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T d K M s₀ : ℕ) [NeZero K] (γ ρ : ℝ)
        (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (x : Ω → Fin T → Fin K → Fin d → ℝ) (ξ : Ω → Fin T → ℝ) (θstar : Fin d → ℝ)
        (sel : LassoSelector T s₀ M d),
        Standing A ε β p γ ρ P x ξ θstar sel →
          Integrable (fun ω => regret (x ω) θstar (action s₀ M sel (x ω) (ξ ω) θstar)) P ∧
          ∫ ω, regret (x ω) θstar (action s₀ M sel (x ω) (ξ ω) θstar) ∂P ≤
            C * regretRate T d K M s₀ γ ρ := by sorry

end SparseBatchBandit
