-- Prove2me | Theorems.Thm_PackingLPAccel_lemma_3_5
-- name    : PackingLPAccel.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:02.131519+00:00
-- url     : https://prove2.me/theorems/cd88eff2-f672-4b78-b4ff-8a499126e056
-- title:
--   Lemma 3.5 — the reduction to $\lceil\log_2 n\rceil+2$ packing LP $\ell_{1,\infty}$ instances (corrected: instances without empty rows)
-- statement:
--   Let $A\in\mathbb R^{m\times n}_{\ge0}$ with $n\ge1$ satisfy the normalization $\min_j\|A_{:,j}\|_\infty=1$, let $\epsilon>0$, and let $i^*(j)$ be a maximizer of $A_{i,j}$ over $i$. Then $\mathrm{OPT}\in[1,n]$, each $I(\lambda)$ with $\lambda>0$ is a valid instance of Problem 1.2, and it is a packing LP $\ell_{1,\infty}$ instance when $A$ has no empty row. Let $T=\lceil\log_2n\rceil+2$, and for each $\tau<T$ let $x^{(\tau)}$ have relative-additive error $(\epsilon/4,\epsilon/(8n))$ for $I(2^\tau)$ against some minimizer. Then every
--
--   $$\hat x^{(\tau)}=\frac{x^{(\tau)}}{\max\{1,\|Ax^{(\tau)}\|_\infty\}}$$
--
--   is feasible for (1), and the best of them satisfies $\langle\mathbf 1,\hat x^{(\tau)}\rangle\ge(1-\epsilon)\mathrm{OPT}$.
--
--   Moreover one program, given $A$ in sparse form, $\epsilon$, and the solver as an oracle, outputs such a point with at most $T$ oracle calls, in work $\widetilde O(\mathrm{nnz}(A))$ and depth $\widetilde O(1)$.
--
--   This is the first reduction of the mission: it turns the constrained packing LP into logarithmically many penalized $\ell_{1,\infty}$ problems.
--
--   Differences from the source:
--   - correction: every I(λ) is a packing LP ℓ1,∞ instance (proof, p.11) → only when A has no empty row; reason: Definition 3.1 requires no empty rows, and a zero row of A gives a zero row of B, so the printed claim fails on A with a zero row
--   - reading: A ∈ ℝ^{m×n}_{≥0} → A normalized, min_j ∥A_{:,j}∥_∞ = 1; reason: the standing assumption of p.10, stated for the rest of the paper
--   - reading: solving up to relative-additive error → error against some minimizer, for each τ; reason: the weakest input, which makes the lemma strongest
--   - reading: an overhead of Õ(nnz(A)) time and Õ(1) depth → one program with the solver as an oracle at cost (1,1) per call; reason: the oracle's own cost is what the overhead excludes
--   - generalization: OPT ∈ [1,n] is a fact quoted on p.9; validity of I(λ) is implicit → both are clauses of the conclusion; reason: they are what the reduction uses
--   - encoding: T = O(log n), I(2^{τ−1}) for τ ∈ [T] → T = ⌈log₂ n⌉+2, I(2^τ) for τ < T; reason: the values of the proof, with a shifted index
--   - reading: "There is a … algorithm", PRAM, the list of p.8 → one program of the language Stmt/Eval (CREW, snapshot parFor, exclusive write), with no log, exp, floor or integer multiplication; reason: the paper names only PRAM and the p.8 list; the list is taken literally, as the non-weaker reading, although the paper's proof evaluates log (p.28)
--   - generalization: the input is A → every enumeration of the nonzero entries, in any order; reason: a fixed order is one such enumeration
--   - encoding: Õ(·) → C·(…)·lg(·)^K with lg(s) = ⌊log₂ s⌋+1 and C, K after the program, before the instance; reason: the meaning of Õ on p.1 and p.8
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Lemma 3.5, p.11 (pdf 12), with the Fact on p.9 (pdf 10)

import Mathlib
import Definitions.Def_PackingLPAccel_CompositeL1Inf

namespace PackingLPAccel

/-- **Lemma 3.5** (manuscript sha256 1dac7711…, p.11). For normalized `A`, the reduction of the packing
LP to `⌈log₂ n⌉ + 2` packing LP `ℓ₁,∞` instances.

**Formalization Note.** Part 1 is the mathematics: the instances `I(2^τ)` (the paper's
`I(2^{τ-1})`, `τ ∈ [T]`) are packing LP `ℓ₁,∞` instances when `A` has no empty row, `OPT ∈ [1, n]`
(Fact 2.1 in [AZO19], p.9), every rescaled `x̂^{(τ)}` is feasible, and the best one is
`(1-ε)`-optimal. Part 2 is the "additional overhead" clause: a program with the solver as an oracle.
The hypothesis that error is measured against **some** minimizer is the weakest reading of the input.
-/
theorem lemma_3_5 :
    (∀ (m n : ℕ) (_ : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (_ : ∀ i j, 0 ≤ A i j)
        (_ : IsNormalized A) (iStar : Fin n → Fin m) (_ : ∀ j i, A i j ≤ A (iStar j) j)
        (ε : ℝ) (_ : 0 < ε),
      ((∀ i, ∃ j, A i j ≠ 0) → ∀ lam : ℝ, 0 < lam →
        (packingInstance A iStar lam).IsPackingL1Inf) ∧
      (∀ lam : ℝ, 0 < lam → (packingInstance A iStar lam).IsValid) ∧
      1 ≤ packingOpt A ∧ packingOpt A ≤ n ∧
      ∀ x : Fin (lemma35Count n) → Fin n → ℝ,
        (∀ τ : Fin (lemma35Count n),
          (packingInstance A iStar (2 ^ (τ : ℕ))).Mem (packingEmbed A (x τ)) ∧
          ∃ Xs, (packingInstance A iStar (2 ^ (τ : ℕ))).IsMinimizer Xs ∧
            (packingInstance A iStar (2 ^ (τ : ℕ))).ErrorAgainst (ε / 4) (ε / (8 * n))
              (packingEmbed A (x τ)) Xs) →
        (∀ τ, Feasible A (rescale A (x τ))) ∧
        ∃ τ, (1 - ε) * packingOpt A ≤ ∑ j, rescale A (x τ) j) ∧
    (∃ P : Stmt, ∃ C K : ℕ,
      ∀ (m n : ℕ) (_ : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (_ : ∀ i j, 0 ≤ A i j)
        (_ : IsNormalized A) (iStar : Fin n → Fin m) (_ : ∀ j i, A i j ≤ A (iStar j) j)
        (ε : ℝ) (_ : 0 < ε) (N : ℕ) (e : Fin N → Fin m × Fin n) (_ : IsNonzeroEnum A e)
        (O : OracleModel) (_ : IsL1InfOracle A iStar ε O),
      ∃ (s' : State) (w d : ℕ), Eval O P (goalInit A ε e) s' w d ∧
        Feasible A (goalOutput N s') ∧
        (1 - ε) * packingOpt A ≤ ∑ j, goalOutput (n := n) N s' j ∧
        s'.calls ≤ lemma35Count n ∧
        (w : ℝ) ≤ C * N * (lg (m + n) : ℝ) ^ K ∧
        (d : ℝ) ≤ C * (lg (m + n) : ℝ) ^ K) := by sorry

end PackingLPAccel
