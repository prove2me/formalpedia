-- Prove2me | Theorems.Thm_PackingLPAccel_theorem_5_5
-- name    : PackingLPAccel.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:36.995926+00:00
-- url     : https://prove2.me/theorems/6c38f0b3-3459-415b-9654-d44468ecccba
-- title:
--   Theorem 5.5 — the box-simplex optimizer with a best response oracle, cited from [CGS25] (corrected: factor $1+\epsilon^{-1}$)
-- statement:
--   Let $(U,\Delta^m,A)$ be a constrained box-simplex game with $U\subseteq\mathbb R^n_{\ge0}$ nonempty, convex and compact, $A\ne0$, and $\psi:\mathbb R^n\to\mathbb R$ convex. Let $\rho>0$ with $\rho\ge\max_{u\in U}\||A|u\|_\infty$, let $R_U\ge\mathrm{Diam}(U)$, and let $r=r_{\alpha,\xi}$ with $\xi=\min(1/m,\rho/(mn\|A\|_\infty))$, $\alpha=16\rho B$ and $B=1+\log\max(1/\xi,R_U+\xi)$. One program, assuming a $\delta_{\mathrm{BR}}$-ABRO for $(U,\psi,r)$ queried only at $(v,h_U)$ with $v\in\Delta^m$ and $\|h_U\|_\infty\le3nB\|A\|_\infty$, outputs $\hat u\in U$, $\hat v\in\Delta^m$ with
--
--   $$\langle v,A\hat u\rangle+\psi(\hat u)\le\langle\hat v,Au\rangle+\psi(u)+\epsilon\rho+6\delta_{\mathrm{BR}}\qquad\forall u\in U,\ v\in\Delta^m.$$
--
--   It uses $\widetilde O(B(1+\epsilon^{-1}))$ oracle calls, work $\widetilde O((\mathrm{nnz}(A)+m+n)B(1+\epsilon^{-1}))$ and depth $\widetilde O(B(1+\epsilon^{-1}))$.
--
--   This cited result supplies the $\epsilon^{-1}$ iteration count of the framework. The program sees $U$ and $\psi$ only through the oracle.
--
--   Differences from the source:
--   - correction: Õ(·ε⁻¹) for every ε > 0 → the factor 1 + ε⁻¹; reason: any run has depth at least 1 while Cε⁻¹polylog(m,n) < 1 for large ε at fixed m, n; for ε ≤ 1 the factor is at most 2ε⁻¹
--   - generalization: no depth clause in Theorem 5.5 → depth ≤ C·B·(1+ε⁻¹)·lg^K; reason: Lemma 5.2 reads Õ(ε⁻¹) depth off this theorem; [CGS25] is not held, so this was not checked against it
--   - reading: U ⊆ ℝⁿ_{≥0}, ρ ≥ max_{u∈U}, Diam(U), arg min in Definition 5.3 → U nonempty, convex and compact; reason: the printed max, Diam and arg min presuppose attainment for every linear term; blocks of Problem 1.2 and the set S are compact
--   - reading: ψ : U → ℝ in Definition 5.3, ψ : ℝⁿ → ℝ in (10) → ψ convex on ℝⁿ, as in (10); reason: the theorem is about the game (10)
--   - encoding: constant c ∈ [1/2,1] in the oracle → c = 1; reason: the convention stated on p.20
--   - encoding: "ρ > 0", A ≠ 0, ε ≤ poly are implicit → 0 < ρ, A ≠ 0; ε⁻¹ ≤ (m+n)^c for every c; reason: ξ = min(1/m, ρ/(mn∥A∥_∞)) needs ρ > 0 and ∥A∥_∞ ≠ 0, so A = 0 is an undefined case; footnote 2, p.1
--   - reading: "There is a … algorithm", PRAM, the list of p.8 → one program of the language Stmt/Eval (CREW, snapshot parFor, exclusive write), with no log, exp, floor or integer multiplication; reason: the paper names only PRAM and the p.8 list; the list is taken literally, as the non-weaker reading, although the paper's proof evaluates log (p.28)
--   - generalization: the input is A → every enumeration of the nonzero entries, in any order; reason: a fixed order is one such enumeration
--   - encoding: Õ(·) → C·(…)·lg(·)^K with lg(s) = ⌊log₂ s⌋+1 and C, K after the program, before the instance; reason: the meaning of Õ on p.1 and p.8
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Theorem 5.5, p.20 (pdf 21), cited there as Theorem 3.2 in [CGS25]; display (10), p.19 (pdf 20)

import Mathlib
import Definitions.Def_PackingLPAccel_BoxSimplex

namespace PackingLPAccel

/-- **Theorem 5.5** (manuscript sha256 1dac7711…, p.20), cited there as Theorem 3.2 in [CGS25].

**Formalization Note.** `U` is compact since `max_{u∈U}`, `Diam(U)` and `arg min` of Definition 5.3 presuppose
attainment; `ψ : ℝⁿ → ℝ` is convex as in display (10), hence continuous. The program reads `A`, `ρ`, `R_U`, `ε`,
and sees `U` and `ψ` only through the oracle. The depth clause is not printed; Lemma 5.2's proof reads the depth
off this theorem. As in Theorem 1.1, the factor is `1 + ε⁻¹`, because a bound below one call is impossible for
large `ε`. -/
theorem theorem_5_5 :
    ∃ P : Stmt, ∀ c : ℕ, ∃ C K : ℕ,
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (_ : A ≠ 0)
        (U : Set (Fin n → ℝ)) (_ : U.Nonempty) (_ : Convex ℝ U) (_ : IsCompact U)
        (_ : ∀ u ∈ U, ∀ j, 0 ≤ u j)
        (ψ : (Fin n → ℝ) → ℝ) (_ : ConvexOn ℝ Set.univ ψ)
        (ρ RU : ℝ) (_ : 0 < ρ) (_ : ∀ u ∈ U, ∀ i, ∑ j, |A i j| * u j ≤ ρ) (_ : euclDiam U ≤ RU)
        (δBR : ℝ) (_ : 0 < δBR)
        (ε : ℝ) (_ : 0 < ε) (_ : ε⁻¹ ≤ ((m + n : ℕ) : ℝ) ^ c)
        (N : ℕ) (e : Fin N → Fin m × Fin n) (_ : IsNonzeroEnum A e)
        (O : OracleModel) (_ : IsABROOracle A U ψ ρ RU δBR O),
      ∃ (s' : State) (w d : ℕ), Eval O P (boxSimplexInit A ε ρ RU e) s' w d ∧
        ∃ (uhat : Fin n → ℝ) (vhat : Fin m → ℝ),
          (∀ j : Fin n, uhat j = s'.M (3 + (N : ℤ) + ((j : ℕ) : ℤ))) ∧
          (∀ i : Fin m, vhat i = s'.M (3 + (N : ℤ) + (n : ℤ) + ((i : ℕ) : ℤ))) ∧
          uhat ∈ U ∧ vhat ∈ stdSimplex ℝ (Fin m) ∧
          (∀ u ∈ U, ∀ v ∈ stdSimplex ℝ (Fin m),
            ∑ i, v i * ∑ j, A i j * uhat j + ψ uhat ≤
              ∑ i, vhat i * ∑ j, A i j * u j + ψ u + ε * ρ + 6 * δBR) ∧
          (s'.calls : ℝ) ≤ C * bsB A ρ RU * (1 + ε⁻¹) * (lg (m + n) : ℝ) ^ K ∧
          (w : ℝ) ≤ C * ((N + m + n : ℕ) : ℝ) * bsB A ρ RU * (1 + ε⁻¹) * (lg (m + n) : ℝ) ^ K ∧
          (d : ℝ) ≤ C * bsB A ρ RU * (1 + ε⁻¹) * (lg (m + n) : ℝ) ^ K := by sorry

end PackingLPAccel
