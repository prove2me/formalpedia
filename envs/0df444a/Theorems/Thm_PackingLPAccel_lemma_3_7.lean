-- Prove2me | Theorems.Thm_PackingLPAccel_lemma_3_7
-- name    : PackingLPAccel.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:11.784815+00:00
-- url     : https://prove2.me/theorems/2f2957a9-dce4-42ea-9a1a-509346d7a3aa
-- title:
--   Lemma 3.7 — solving $I(\lambda)$ by $\widetilde O(\epsilon^{-1})$ residual problems (corrected: residual and factor $1+\epsilon^{-1}$)
-- statement:
--   One program does the following for every normalized $A\ge0$, every instance $I(2^\tau)$ of Lemma 3.5, every $\epsilon,\delta>0$ with $\epsilon^{-1},\delta^{-1}\le(m+n)^c$, and every $\kappa\in[1,\mathsf{lg}(m+n)^{b_\kappa}]$. Given $A$ in sparse form, $\epsilon,\delta,\kappa,\lambda$, and a residual solver as an oracle, it outputs a point $x$ of the box with relative-additive error $(\epsilon,\delta)$ against every minimizer of $I(2^\tau)$:
--
--   $$\mathcal E_{1,\infty}(Y(x))\le\psi(X^\star)+(1+\epsilon)\|X^\star\|_{1,\infty}+\delta.$$
--
--   Every query it makes is an allowed residual query, i.e. a quasi-poly-bounded instance of Problem 1.3 in the corrected explicit form, asked up to multiplicative factor $\kappa$ and additive error at least $(m+n)^{-c'}$. It makes $\widetilde O(1+\epsilon^{-1})$ calls, with overhead work $\widetilde O(\mathrm{nnz}(A)(1+\epsilon^{-1}))$ and depth $\widetilde O(1+\epsilon^{-1})$.
--
--   This lemma absorbs Lemmas 5.2 and 5.8 and the iterative refinement. It is where the $\epsilon^{-1}$ of the main theorem appears.
--
--   Differences from the source:
--   - correction: the residual (21)–(22) in the proof → the corrected c_ij and v^{(2)} in the query forms; reason: same counterexample as Lemma 5.14: on E(x) = x⁴ the printed residual has minimum 0 at ∆ = 0
--   - correction: Õ(·ε⁻¹) for every ε > 0 → the factor 1 + ε⁻¹; reason: any run has depth at least 1 while Cε⁻¹polylog(m,n) < 1 for large ε at fixed m, n; for ε ≤ 1 the factor is at most 2ε⁻¹
--   - generalization: every query is a quasi-poly-bounded instance of Problem 1.3 → queries lie in a narrower class: the explicit forms of pp.27–28 with numeric bounds; reason: the program promises more about its queries; decomposability (Lemma 5.16) and ∥Â∥_∞ ≤ 1 hold for those forms and are not stated
--   - reading: the proof's "∥A∥_∞ = 1" (p.28) → the query's matrix is Â_ij = A_ij/∥A_{:,j}∥_∞ with u_j = 1; reason: ∥A∥_∞ = 1 does not follow from min_j ∥A_{:,j}∥_∞ = 1, and L_j would grow with the width; Definition 3.1 allows the rescaling
--   - reading: (Õ(1), 1/poly(m,n)) error → κ ≤ lg(m+n)^{bκ} as an input, for every bκ, and δ_res ≥ (m+n)^{−c'}; reason: b, c', C, K are chosen after c and bκ
--   - reading: relative-additive error (ε,δ) → against every minimizer; reason: the strong reading of X⋆ = arg min
--   - encoding: an instance constructed by Lemma 3.5 → I(2^τ), τ < ⌈log₂ n⌉+2, A normalized, λ as an input; reason: the instances of that lemma
--   - reading: "There is a … algorithm", PRAM, the list of p.8 → one program of the language Stmt/Eval (CREW, snapshot parFor, exclusive write), with no log, exp, floor or integer multiplication; reason: the paper names only PRAM and the p.8 list; the list is taken literally, as the non-weaker reading, although the paper's proof evaluates log (p.28)
--   - generalization: the input is A → every enumeration of the nonzero entries, in any order; reason: a fixed order is one such enumeration
--   - encoding: Õ(·) → C·(…)·lg(·)^K with lg(s) = ⌊log₂ s⌋+1 and C, K after the program, before the instance; reason: the meaning of Õ on p.1 and p.8
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Lemma 3.7, p.12 (pdf 13); proof pp.27–28 (pdf 28–29)

import Mathlib
import Definitions.Def_PackingLPAccel_ResidualQuery

namespace PackingLPAccel

/-- **Lemma 3.7, corrected residual** (manuscript sha256 1dac7711…, p.12; proof pp.27–28).

**Formalization Note.** One program solves each instance `I(2^τ)` of Lemma 3.5, given a residual solver as an
oracle. `Õ(1)` in the query class and the multiplicative error is `lg(m+n)^b`: the constant `bκ` is free and the
class's `b`, `c'` are chosen after it. "Quasi-poly-bounded" is `IsAllowedQuery`, whose function forms carry the corrected
residual. Decomposability and `∥A∥_∞ ≤ poly` are not required of the queries, which only strengthens the theorem.
Conclusion: the output has relative-additive error `(ε, δ)` against **every** minimizer. As in
Theorem 1.1, the factor is `1 + ε⁻¹`. -/
theorem lemma_3_7 :
    ∃ P : Stmt, ∀ c bκ : ℕ, ∃ C K b c' : ℕ,
      ∀ (m n : ℕ) (_ : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (_ : ∀ i j, 0 ≤ A i j)
        (_ : IsNormalized A) (iStar : Fin n → Fin m) (_ : ∀ j i, A i j ≤ A (iStar j) j)
        (τ : ℕ) (_ : τ < lemma35Count n)
        (ε δ κ : ℝ) (_ : 0 < ε) (_ : 0 < δ) (_ : ε⁻¹ ≤ ((m + n : ℕ) : ℝ) ^ c)
        (_ : δ⁻¹ ≤ ((m + n : ℕ) : ℝ) ^ c) (_ : 1 ≤ κ) (_ : κ ≤ (lg (m + n) : ℝ) ^ bκ)
        (N : ℕ) (e : Fin N → Fin m × Fin n) (_ : IsNonzeroEnum A e)
        (O : OracleModel) (_ : IsResidualSolver A b c' κ O),
      ∃ (s' : State) (w d : ℕ), Eval O P (lemma37Init A ε δ κ (2 ^ τ) e) s' w d ∧
        (packingInstance A iStar (2 ^ τ)).Mem (packingEmbed A (lemma37Output N s')) ∧
        (∀ Xs, (packingInstance A iStar (2 ^ τ)).IsMinimizer Xs →
          (packingInstance A iStar (2 ^ τ)).ErrorAgainst ε δ
            (packingEmbed A (lemma37Output N s')) Xs) ∧
        (s'.calls : ℝ) ≤ C * (1 + ε⁻¹) * (lg (m + n) : ℝ) ^ K ∧
        (w : ℝ) ≤ C * N * (1 + ε⁻¹) * (lg (m + n) : ℝ) ^ K ∧
        (d : ℝ) ≤ C * (1 + ε⁻¹) * (lg (m + n) : ℝ) ^ K := by sorry

end PackingLPAccel
