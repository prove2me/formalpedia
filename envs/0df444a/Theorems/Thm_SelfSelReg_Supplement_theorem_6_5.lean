-- Prove2me | Theorems.Thm_SelfSelReg_Supplement_theorem_6_5
-- name    : SelfSelReg.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:19:32.632617+00:00
-- url     : https://prove2.me/theorems/e5f7aefa-8a2f-4d85-af1f-a7c5a04cff92
-- title:
--   Theorem 6.5 — observable-operator construction
-- statement:
--   Work in the setting of Section 6: the Gaussian self-selection model with regressors $w_1,\dots,w_k\in\mathbb R^n$, $2\le k\le n$, under Assumption 1.2 with constants $B\ge1$, $\Delta\in(0,1]$, and the hyperparameters $K$, $s$, $T$. Fix a non-empty $Q\subseteq[k]$ and consider the rank-one sums $A_Q^{(s)}$ and $M_Q^{(s)}(b)$ of (38), built from the weights $\lambda_i^{(2s)}$, the unit regressors $u_i$ and the scaled regressors $a_i$. Let $C_s\in\mathbb R^{p\times n^s}$ have orthonormal rows for some $1\le p\le|Q|$, and let $\varepsilon_{\mathrm{mom}},\varepsilon_{\mathrm{proj}},\varepsilon_\perp\ge0$. Suppose:
--
--   1. $\|a_i\|_2\le K^3$ for every $i\in Q$;
--   2. $\bigl\|(\langle u_i^{\otimes s},u_j^{\otimes s}\rangle)_{i,j\in Q}-I\bigr\|_{\mathrm{op}}\le\varepsilon_\perp$;
--   3. the symmetric matrices $\widehat A,\widehat M_1,\dots,\widehat M_n\in\mathbb R^{p\times p}$ form an $\varepsilon_{\mathrm{mom}}$-estimate of the projected moment matrices for $Q$ relative to $C_s$ (Definition 6.2);
--   4. $\bigl\|(I-C_s^\top C_s)(A_Q^{(s)})^{1/2}\bigr\|_{\mathrm{op}}^2\le\varepsilon_{\mathrm{proj}}\operatorname{tr}(A_Q^{(s)})$;
--   5. $\varepsilon_{\mathrm{mom}}+\varepsilon_{\mathrm{proj}}+\varepsilon_\perp\le\dfrac1{16k^2}$.
--
--   Then CONSTRUCTOBSERVABLEOPERATORS (Algorithm 6.2), given $\widehat A,\widehat M_1,\dots,\widehat M_n$, returns a dimension $i_\star$ and matrices $\widehat D_1,\dots,\widehat D_n\in\mathbb R^{i_\star\times i_\star}$ that form a
--
--   $$
--   16K^3k^3\bigl(\varepsilon_{\mathrm{mom}}+\varepsilon_{\mathrm{proj}}+\varepsilon_\perp\bigr)\text{-approximate observable-operator family}
--   $$
--
--   (Definition 6.4) for $(a_i)_{i\in J}$, for some non-empty $J\subseteq Q$ with $|J|=i_\star$. Moreover, the routine runs in $\mathrm{poly}(n,k)$ time.
--
--   The theorem converts moment estimates into matrices whose common eigenvectors and eigenvalues encode a block of scaled regressors; Theorem 6.6 then decodes them.
--
--   **Formalization Note** The statement has two parts. (1) Correctness holds for every output of Algorithm 6.2, that is for every choice of orthonormal eigenvectors of $\widehat A$ and of the maximizing eigengap. (2) Running time: there are one program and one constant $C$ such that on all symmetric inputs of dimension $p\le k$ the program halts within $C(n+k)^C$ units of work with an output of Algorithm 6.2. The program runs on the published unit-cost real RAM with square roots and a symmetric eigensolver charged $d^3+1$ on a $d\times d$ matrix.
--
--   Differences from the source:
--
--   - reading: "Fix a non-empty Q ⊆ [k]. Consider the rank-one sums A_Q^{(s)}, M_Q^{(s)}(b) from (38)", with K, without restating the model → the setting of Section 6 is assumed: the model with 2 ≤ k ≤ n under Assumption 1.2 with B ≥ 1, ∆ ∈ (0, 1], and K, s, T of Hyperparameters 4.1; reason: the sums (38) are built from the weights and scaled regressors of the model, and the proof uses λ_i^{(2s)} > 0 "by Theorem 5.1(ii)" (p.40) and K ≥ 1; without positive weights the square root in (d) need not exist
--   - encoding: CONSTRUCTOBSERVABLEOPERATORS (Algorithm 6.2) returns a family → every pair (i⋆, D̂) in the input–output relation of Algorithm 6.2 (any orthonormal eigenvectors of Â, any maximizer of the clipped gap) is such a family for some non-empty J ⊆ Q with |J| = i⋆; reason: the pseudocode fixes neither the eigenvectors nor the tie-break; quantifying over all of them covers every implementation
--   - reading: "the routine runs in poly(n, k) time", no machine named; the proof counts the eigendecomposition as a polynomial-time step → one program of the published unit-cost real RAM with √ and a charged exact symmetric eigensolver (cost d³ + 1), and one constant C, such that on all symmetric inputs with 1 ≤ p ≤ k it halts within C(n + k)^C work with an output of Algorithm 6.2; reason: the conclusion is exact when the three errors vanish, and exact eigenvectors are not computable from + − × ÷ √ and comparisons, so the arithmetic-only machine of the published goal cannot return an output of Algorithm 6.2; the eigensolver step is the one the paper itself counts
--   - encoding: Λ̂^{−1/2} in line 7 of Algorithm 6.2, defined only when λ̂_{i⋆} > 0 → the relation of Algorithm 6.2 uses (√λ̂)⁻¹ with Lean's 0⁻¹ = 0, so when λ̂_{i⋆} = 0 its outputs are the zero matrices; reason: under (a)–(e) the paper proves λ̂_{i⋆} > 0 ((70), p.42), so no instance of the correctness part changes; in the running-time part, which holds for all symmetric inputs, the convention only fixes the output where the pseudocode divides by zero
--   - encoding: s := K⁴ log n (Hyperparameters 4.1), used as a tensor order → s = ⌈K⁴ log n⌉ (the published hypS); reason: the convention of the published base mission; (182) states s ≤ 2K⁴ log n
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 6.5, pp.30–31 (PDF pp.33–34); Algorithm 6.2, p.39 (PDF p.42)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Machine
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_restrictedMoment
import Definitions.Def_SelfSelReg_Supplement_Routine
import Definitions.Def_SelfSelReg_Supplement_ProjectedMoments
import Definitions.Def_SelfSelReg_Supplement_ObservableFamily
import Definitions.Def_SelfSelReg_Supplement_EigDecomp
import Definitions.Def_SelfSelReg_Supplement_ConstructObservableOperators

open scoped Matrix.Norms.L2Operator

namespace SelfSelReg

namespace Supplement

/-- **Theorem 6.5** (Observable-Operator Construction).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 6.5, pp.30–31 (PDF pp.33–34); Algorithm 6.2, p.39
(PDF p.42): "Fix a non-empty Q ⊆ [k]. Consider the rank-one sums A^{(s)}_Q, M^{(s)}_Q(b) from (38). Let
C_s ∈ ℝ^{p_s×n^s} have orthonormal rows for some 1 ≤ p_s ≤ |Q| and ε_mom, ε_proj, ε_⊥ ≥ 0. Suppose the
following conditions hold. (a) For every i ∈ Q, ‖a_i‖₂ ≤ K³. (b) The lifted vectors satisfy
‖(⟨u_i^{⊗s}, u_j^{⊗s}⟩)_{i,j∈Q} − I‖_op ≤ ε_⊥ (42). (c) The matrices Â, M̂_1, …, M̂_n form an ε_mom-estimate
of the projected moment matrices for Q relative to C_s (Definition 6.2). (d) The projection error
satisfies ‖(I − C_sᵀC_s)(A^{(s)}_Q)^{1/2}‖²_op ≤ ε_proj tr(A^{(s)}_Q) (43). (e) The errors satisfy
ε_mom + ε_proj + ε_⊥ ≤ 1/(16k²). Then CONSTRUCTOBSERVABLEOPERATORS (Algorithm 6.2), given these matrices,
returns a 16K³k³(ε_mom + ε_proj + ε_⊥)-approximate observable-operator family (Definition 6.4) for
(a_i)_{i∈J} indexed by some J ⊆ Q. Moreover, the routine runs in poly(n, k) time."

The statement has two parts.

1. **Correctness.** In the setting of §6 (the model with `2 ≤ k ≤ n` under Assumption 1.2, and
   `K, s, T` of Hyperparameters 4.1), under (a)–(e), **every** output `(i⋆, D̂)` of Algorithm 6.2 on
   `(Â, M̂)` (`IsConstructOutput`: every choice of eigenvectors and of the maximizing gap) is a
   `16K³k³(ε_mom + ε_proj + ε_⊥)`-approximate observable-operator family for `(a_i)_{i∈J}`, for some
   non-empty `J ⊆ Q` with `|J| = i⋆`.
2. **Running time.** One program `P` and one constant `C`: on all symmetric inputs
   `Â, M̂_1, …, M̂_n ∈ ℝ^{p×p}` with `1 ≤ p ≤ k`, `P` halts within `C (n + k)^C` units of work and its
   output is an output of Algorithm 6.2.

**Formalization Note.**
* The weights `λ_i^{(2s)}`, the scaled regressors `a_i` and `u_i` in (38) are those of the model, and
  the proof uses `λ_i^{(2s)} > 0` "by Theorem 5.1(ii)" (p.40, PDF p.43) and `K ≥ 1`; so the setting of
  §6 is part of part 1. Hypothesis (c) carries the symmetry of `Â, M̂_ℓ` and the orthonormality of the
  rows of `C_s` (Definition 6.2).
* The running time is counted as the paper counts it, with the eigendecomposition of line 1 as a
  polynomial-time step ("All matrices used by the routine have dimension at most p_s ≤ |Q| ≤ k, so
  it runs in poly(n, k) time", p.42, PDF p.45): `P` is a program of the published unit-cost real RAM
  with a charged exact symmetric eigensolver, `ExpanderWalkDecode.Main` (`eig` on a `d × d` matrix
  costs `d³ + 1`; `√` is an instruction). Exact eigenvectors are not computable from `+ − × ÷ √` and
  comparisons, and the conclusion of part 1 is exact when `ε_mom = ε_proj = ε_⊥ = 0`, so no program
  without such a step returns an output of Algorithm 6.2.
* Input: real bank `0` holds `Â`, then `M̂_1, …, M̂_n`, each row by row; integer bank `0` holds `n, p`.
  Output list: `i⋆`, then `D̂_1, …, D̂_n` row by row. The routine is deterministic: `RunsWithin … 1`
  asks for a correct output on every coin tape. -/
theorem theorem_6_5 :
    (∀ (n k : ℕ), 2 ≤ k → k ≤ n →
      ∀ (B Δ : ℝ), 1 ≤ B → 0 < Δ → Δ ≤ 1 →
      ∀ w : Fin k → EuclideanSpace ℝ (Fin n), SatisfiesAssumption B Δ w →
      ∀ Q : Finset (Fin k), Q.Nonempty →
      ∀ p : ℕ, 1 ≤ p → p ≤ Q.card →
      ∀ (Cs : Matrix (Fin p) (Fin (hypS B Δ n) → Fin n) ℝ) (εmom εproj εperp : ℝ),
        0 ≤ εmom → 0 ≤ εproj → 0 ≤ εperp →
      ∀ (Ahat : Matrix (Fin p) (Fin p) ℝ) (Mhat : Fin n → Matrix (Fin p) (Fin p) ℝ),
        (∀ i ∈ Q, ‖scaledReg w (hypT B Δ n) (hypS B Δ n) i‖ ≤ hypK B Δ ^ 3) →
        ‖liftedGram w Q (hypS B Δ n) - 1‖ ≤ εperp →
        IsProjectedMomentEstimate w (hypT B Δ n) Q Cs Ahat Mhat εmom →
        ProjectionError Cs (evenTarget w (hypT B Δ n) Q (hypS B Δ n))
          (εproj * Matrix.trace (evenTarget w (hypT B Δ n) Q (hypS B Δ n))) →
        εmom + εproj + εperp ≤ 1 / (16 * (k : ℝ) ^ 2) →
        ∀ (iStar : ℕ) (D : Fin n → Matrix (Fin iStar) (Fin iStar) ℝ),
          IsConstructOutput Ahat Mhat iStar D →
          ∃ (J : Finset (Fin k)) (hJ : J.card = iStar), J.Nonempty ∧ J ⊆ Q ∧
            IsApproxObservableFamily (scaledReg w (hypT B Δ n) (hypS B Δ n)) J hJ D
              (16 * hypK B Δ ^ 3 * (k : ℝ) ^ 3 * (εmom + εproj + εperp))) ∧
    ∃ (P : ExpanderWalkDecode.Main.Program) (_ : ExpanderWalkDecode.Main.Admissible P) (C : ℕ),
      ∀ (n k p : ℕ), 1 ≤ n → 1 ≤ p → p ≤ k →
      ∀ (Ahat : Matrix (Fin p) (Fin p) ℝ) (Mhat : Fin n → Matrix (Fin p) (Fin p) ℝ),
        Ahat.IsHermitian → (∀ l, (Mhat l).IsHermitian) →
        ExpanderWalkDecode.Main.RunsWithin P
          (ExpanderWalkDecode.Main.init
            (fun bank => if bank = 0 then
                ExpanderWalkDecode.Main.listBank
                  (matData Ahat ++ (List.ofFn fun l => matData (Mhat l)).flatten)
              else fun _ => 0)
            (fun bank => if bank = 0 then ExpanderWalkDecode.Main.listIBank [(n : ℤ), (p : ℤ)]
              else fun _ => 0))
          (C * ((n : ℝ) + k) ^ C)
          (fun out => ∃ (iStar : ℕ) (D : Fin n → Matrix (Fin iStar) (Fin iStar) ℝ),
            out = (iStar : ℝ) :: (List.ofFn fun l => matData (D l)).flatten ∧
            IsConstructOutput Ahat Mhat iStar D)
          1 := by sorry

end Supplement

end SelfSelReg
