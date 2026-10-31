-- Prove2me | Theorems.Thm_TransitoryQueue_exists_strong_coupling
-- name    : TransitoryQueue.exists_strong_coupling
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:04:02.019953+00:00
-- url     : https://prove2.me/theorems/883b23ee-b783-4806-b22a-8cbd4a8571b0
-- title:
--   §2.2 — one version carries all three couplings
-- statement:
--   Let $F_n$ ($n\ge1$) and $G$ be distribution functions supported on $[0,\infty)$ with $\sup_{t\ge0}|F_n(t)-G(t)|=O(1/\sqrt n)$, let $p\in[0,1]$, and let $\nu$ be a law on $[0,\infty)$ whose moment generating function is finite near $0$, with mean $\mu>0$ and standard deviation $\sigma$. Then there is a probability space carrying a version of the RS$(G,p)/G/1$ primitives and of the Gaussian processes that is **strongly coupled**: arrival epochs iid $F_n$, turn-up indicators iid Bernoulli($p$), service requirements iid $\nu$, Brownian motions $B,\hat B$ common to all $n$, one Brownian bridge for all $n$, the three blocks independent, and the couplings (88), (89), (98) hold with constants $C,K,\lambda$ independent of $n$.
--
--   This formalizes §2.2: "the same version suffices for each theorem below".
--
--   Differences from the source:
--   - generalization: (88) at the random index nG_n(t), (98) at the random index A_n(t) → (88) and (98) at every index k ≤ n; reason: the bound at every k implies the bound at any random index
--   - reading: "the same version suffices for each theorem below"; B^{br,n} a different bridge for each n (Remark 3.4) → one version on one space, with one bridge for all n (Remark 8.3), and independent blocks (T, Bbr), (ζ, B̂), (V, B); reason: Remark 8.3 shows one bridge suffices; the independence is what the paper's construction provides
--   - encoding: (88) normalized by √(p(1−p)), (98) by σ → (88) multiplied by √(p(1−p)), (98) by σ; reason: same events when p ∈ (0, 1), σ > 0; no division by zero otherwise
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, §2.2, p.6; eqs. (88), (89), p.31; eq. (98), p.33; Corollary 5.4, p.26; Remark 8.3, p.46

import Mathlib
import Definitions.Def_TransitoryQueue_IsArrivalCDF
import Definitions.Def_TransitoryQueue_IsStrongCoupling
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TransitoryQueue

/-- **One version carries all couplings.** Under the model's assumptions there is a probability
space carrying a version of the RS(G, p)/G/1 primitives and of the Gaussian processes that is
strongly coupled in the sense of (88), (89) and (98), with one Brownian bridge for all `n`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, §2.2, p.6 ("the same version suffices for each theorem below"), with (88), (89), p.31,
(98), p.33, Corollary 5.4, p.26, and Remark 8.3, p.46.

**Formalization Note** The model's hypotheses are those of Theorem 2.11 that concern the
primitives: `F_n` distribution functions, `p ∈ [0, 1]`, `ν` a probability law on `[0, ∞)` with a
finite moment generating function near `0`. -/
theorem exists_strong_coupling (F : ℕ → ℝ → ℝ) (hF : ∀ n, IsArrivalCDF (F n))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hmgf : ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℝ, |l| < δ → Integrable (fun y => Real.exp (l * y)) ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (T : (n : ℕ) → Fin n → Ω → ℝ) (ζ : (n : ℕ) → Fin n → Ω → ℕ) (V : (n : ℕ) → Fin n → Ω → ℝ)
      (B Bh : ℝ≥0 → Ω → ℝ) (Bbr : ℕ → ℝ → Ω → ℝ),
      IsStrongCoupling P F p ν T ζ V B Bh Bbr := by sorry

end TransitoryQueue
