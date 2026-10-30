-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_polynomial_construction_recipes
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.polynomial_construction_recipes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:51:46.484174+00:00
-- url     : https://prove2.me/theorems/824a8b41-95fe-4bdc-9075-36a5011840e9
-- title:
--   Theorem 30: all five polynomial construction recipes
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. Let $J_d(\mathbb C[S_k])$ be the sum of the central-idempotent-generated isotypic ideals indexed by shapes with more than $d$ rows. For constant-coefficient $\alpha$, write $g_\alpha(X)=\operatorname{tr}_{\ne k}[\widehat T(\alpha)(\bigotimes_{i=1}^kX_i)]$ and let $h_\alpha$ contract all input slots against the inputs, retaining all last $t$ output slots with identities there. Support means nonzero coefficient support. The following five recipes hold universally over the complex inputs:
--
--   1. For $k\ge1$ and $\alpha\in J_d$, if every supported permutation is one full cycle acting nontrivially on every slot, $g_\alpha$ is a noncommutative polynomial identity.
--   2. If $\alpha=\beta+\gamma$, every supported permutation of $\beta$ is such a full cycle, and every supported permutation of $\gamma$ fixes some input slot $i<k$, then $g_\beta$ is a noncommutative polynomial vanishing on every traceless input tuple.
--   3. With the same full-cycle condition on $\beta$, if every supported permutation of $\gamma$ fixes slot $k$, then $g_\beta(X_1,\ldots,X_{k-1},I)$ is a noncommutative polynomial taking a scalar multiple of $I$ at every tuple.
--   4. For $k=r+2$, if every supported permutation of $\beta$ has exactly two cycles, each containing exactly one of the last two outputs and acting nontrivially there, and every supported permutation of $\gamma$ has the closed output transposition, then $h_\beta$ is a tensor polynomial taking a scalar multiple of the swap. More generally, for $k=r+t$, $1\le t\le k$, exactly $t$ such output-marked cycles in $\beta$ and a prescribed closed output action $\rho\in S_t$ in $\gamma$ give $h_\beta(X)=c(X)T(\rho)$.
--   5. If $\alpha\in J_d$ is supported on exactly $t$ cycles with exactly one marked output apiece, each output acted on nontrivially, then $h_\alpha$ is a tensor polynomial identity on all $t$ outputs.
--
--   Thus the universal conclusions include
--
--   $$g_\alpha(X)=0,\qquad g_\beta(X)=0\ (\operatorname{tr}X_i=0),\qquad g_\beta(X_1,\ldots,X_{k-1},I)=c(X)I,\qquad h_\beta(X)=c(X)T(\rho),\qquad h_\alpha(X)=0,$$
--
--   under their respective hypotheses. Scalars may be zero, as Definition 29 permits. Formal polynomial evaluation is required in addition to each evaluated identity.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 26, Theorem 30: all five polynomial construction recipes

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Theorem 30, all five construction recipes including the C4 generalization
(PDF pp.25–26). J_d is the independently constructed isotypic-ideal sum.
SOURCE CORRECTION in C5: beta becomes alpha, k−2 arguments become k−t, and all t
output slots are retained. Exactly one output per cycle is enforced. Definition 29
allows the resulting scalar to be zero. -/
theorem polynomial_construction_recipes {d : ℕ} (hd : 0 < d) :
    (∀ (r : ℕ) (a : GroupCoefficients (r+1)), InAntisymmetricIdeal d a →
      ((∀ pi, a pi ≠ 0 → FullNontrivialCycle pi) →
        IsNoncommutativePolynomial (gPolynomial (d := d) a) ∧
        ∀ X : Fin (r+1) → (Matrix (Fin d) (Fin d) ℂ), gPolynomial a X = 0) ∧
      (∀ b c : GroupCoefficients (r+1), a = b+c →
        (∀ pi, b pi ≠ 0 → FullNontrivialCycle pi) →
        (∀ pi, c pi ≠ 0 → ∃ i : Fin (r+1), i ≠ Fin.last r ∧ pi i = i) →
        IsNoncommutativePolynomial (gPolynomial (d := d) b) ∧
        ∀ X : Fin (r+1) → (Matrix (Fin d) (Fin d) ℂ), (∀ i, Matrix.trace (X i) = 0) →
          gPolynomial b X = 0) ∧
      (∀ b c : GroupCoefficients (r+1), a = b+c →
        (∀ pi, b pi ≠ 0 → FullNontrivialCycle pi) →
        (∀ pi, c pi ≠ 0 → pi (Fin.last r) = Fin.last r) →
        IsNoncommutativePolynomial
          (fun X : Fin r → (Matrix (Fin d) (Fin d) ℂ) => gPolynomial b (Fin.lastCases 1 X)) ∧
        ∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ), ∃ z : ℂ,
          gPolynomial b (Fin.lastCases 1 X) = z • (1 : (Matrix (Fin d) (Fin d) ℂ)))) ∧
    (∀ (r : ℕ) (a b c : GroupCoefficients (r+2)),
      InAntisymmetricIdeal d a → a = b+c →
      (∀ pi, b pi ≠ 0 → OutputMarkedCycles (r := r) (t := 2) pi) →
      (∀ pi, c pi ≠ 0 → ClosedOutputAction (r := r) (Equiv.swap (0 : Fin 2) 1) pi) →
      IsTensorPolynomial (hPolynomial (d := d) (r := r) (t := 2) b) ∧
      ∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ), ∃ z : ℂ,
        hPolynomial b X = z • QAlgorithms.Schur.tensorPermutation d 2 (Equiv.swap 0 1)) ∧
    (∀ (r t : ℕ), 1 ≤ t → ∀ (a b c : GroupCoefficients (r+t))
      (rho : Equiv.Perm (Fin t)), InAntisymmetricIdeal d a → a = b+c →
      (∀ pi, b pi ≠ 0 → OutputMarkedCycles (r := r) (t := t) pi) →
      (∀ pi, c pi ≠ 0 → ClosedOutputAction (r := r) rho pi) →
      IsTensorPolynomial (hPolynomial (d := d) (r := r) (t := t) b) ∧
      ∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ), ∃ z : ℂ,
        hPolynomial b X = z • QAlgorithms.Schur.tensorPermutation d t rho) ∧
    (∀ (r t : ℕ), 1 ≤ t → ∀ a : GroupCoefficients (r+t), InAntisymmetricIdeal d a →
      (∀ pi, a pi ≠ 0 → OutputMarkedCycles (r := r) (t := t) pi) →
      IsTensorPolynomial (hPolynomial (d := d) (r := r) (t := t) a) ∧
      ∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ), hPolynomial a X = 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
