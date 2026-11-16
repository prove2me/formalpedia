-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_Supplement_fixed_depth_tradeoff
-- name    : RandomCNFDeficiency.LowerBound.Supplement.fixed_depth_tradeoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:01:36.378196+00:00
-- url     : https://prove2.me/theorems/8a203498-2feb-42f8-83b3-8d7654c7f6ff
-- title:
--   Theorem A.1 — fixed-depth size–degree tradeoff for $\mathrm{AC}^0[p]$-Frege
-- statement:
--   Fix a prime $p$, a finite set $R$ of sound Frege rule schemes, and an integer $\ell\ge2$. Let $F_n$ be a family of unsatisfiable CNF formulas on $n$ variables of width at most $w=w(n)$. Suppose that for some $g=g(n)\ge0$
--
--   $$\operatorname{Deg}_{\mathrm{PC},\mathbb F_p}(F_n)>\frac n2-g\quad\text{(for all large $n$)},\qquad g+w=o\!\left(\frac{n}{(\log n)^{\ell-2}}\right).$$
--
--   Then every depth-$\ell$ $\mathrm{AC}^0[p]$-Frege refutation of $F_n$ has size $n^{\omega_n(1)}$: for every $A>0$, for all sufficiently large $n$, every such refutation has size greater than $n^A$.
--
--   The theorem converts polynomial calculus degree lower bounds very close to $n/2$ into superpolynomial lower bounds for bounded-depth Frege with modular gates, for an arbitrary fixed rule set.
--
--   Differences from the source:
--   - encoding: variables x_1, …, x_n → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - generalization: a fixed finite, sound and implicationally complete collection R of Frege rule schemes → any finite list R of sound de Morgan rule schemes; reason: the proof uses only soundness and finiteness of R (Lemma A.8); every source rule set is such a list
--   - generalization: input clauses and the clausal modular recursion axioms B ∨ ¬U ∨ V etc. as fixed syntactic lines → any formula that is a disjunction of exactly the clause's literals (⊥ for the empty clause), and each modular recursion clause in any order and bracketing of its three disjuncts; reason: more lines are admissible, so more proofs are covered; the source's presentation is one of them
--   - reading: size = total number of symbol occurrences in the sequence → the number of occurrences of constants, variables and connectives (one per MOD gate), summed over all lines; reason: the source does not fix which symbols count; parentheses or separators only enlarge S, so a lower bound on this count implies the same bound for any such convention, and Σ M_i ≤ S still holds
--   - encoding: MOD_{p,a} with a ∈ 𝔽_p, residues taken modulo p → residues a : ZMod p with a - 1 computed in ZMod p; reason: same residues
--   - encoding: Deg_PC,𝔽_p(F) > D → every ordinary PC refutation of F over ZMod p has degree > D, compared in ℝ; reason: the minimum degree exceeds D iff every refutation's degree does
--   - reading: CNF formulas of width w → every clause has width at most w(n); reason: the standard meaning of the width of a CNF; exact width w is included
--   - generalization: Deg_PC,𝔽_p(F_n) > n/2 − g for the family → only for all sufficiently large n; reason: the conclusion is asymptotic
--   - encoding: g + w = o(n/(log n)^{ℓ−2}) → (g + w) =o[atTop] (n / (ln n)^{ℓ−2}) with real natural logarithm; reason: the base of the logarithm changes only a constant factor
--   - encoding: size n^{ω_n(1)} → for every real A > 0, eventually every depth-ℓ refutation has size > n^A; reason: the definition of superpolynomial size
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Theorem A.1, Equation (44), printed p. 20, PDF p. 22; Section 2.3, printed p. 8, PDF p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_ModFrege
import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_PCDerivation
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound

/-- Conneryd, STOC 2027 #332, Theorem A.1 (fixed-depth tradeoff): fix a prime `p`, a finite set
`R` of sound Frege rule schemes and `ℓ ≥ 2`. If unsatisfiable CNFs `F_n` of width `w(n)` satisfy
`Deg_{PC,F_p}(F_n) > n/2 - g(n)` with `g ≥ 0` and `g + w = o(n/(log n)^{ℓ-2})`, then for every
`A > 0`, eventually every depth-`ℓ` AC⁰[p]-Frege refutation of `F_n` has size `> n^A`. -/
theorem fixed_depth_tradeoff (p : ℕ) [Fact p.Prime] (R : List FregeRule)
    (hR : ∀ ρ ∈ R, ρ.Sound) (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (F : (n : ℕ) → CNF n) (w : ℕ → ℕ) (g : ℕ → ℝ)
    (hunsat : ∀ n, ¬ Satisfiable (F n))
    (hwidth : ∀ n, ∀ C ∈ F n, clauseWidth C ≤ w n)
    (hg : ∀ n, 0 ≤ g n)
    (hdeg : ∀ᶠ n : ℕ in Filter.atTop, FpDegreeExceeds p (F n) ((n : ℝ) / 2 - g n))
    (hsmall : (fun n : ℕ => g n + (w n : ℝ)) =o[Filter.atTop]
      (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ) ^ (ℓ - 2))) :
    ∀ A : ℝ, 0 < A → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ π : List (MFormula p (Fin n)), IsFregeRefutation R (F n) π → ProofDepthLE π ℓ →
        (n : ℝ) ^ A < (proofSize π : ℝ) := by sorry

end RandomCNFDeficiency.LowerBound.Supplement
