-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_Supplement_inference_error_derivation
-- name    : RandomCNFDeficiency.LowerBound.Supplement.inference_error_derivation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:04:02.313716+00:00
-- url     : https://prove2.me/theorems/b8375016-add9-437c-848b-eeb1777607d0
-- title:
--   Lemma A.8 — inference errors follow from approximation errors
-- statement:
--   Fix a prime $p$ and a finite set $R$ of sound Frege rule schemes defining, with the modular recursion axioms, $\mathrm{AC}^0[p]$-Frege. There is a constant $B=B(R,p)$ with the following property. Let $\pi$ be an $\mathrm{AC}^0[p]$-Frege proof from a CNF $F$, and assign consistent RS approximators $\mathrm{App}_A$ (Definition A.4, any positive $t_i$ and any coefficient choices) to all syntactic rooted subformulas $A$ of $\pi$, with $\deg\mathrm{App}_A\le\Delta$.
--
--   1. For each non-input inference $L_1,\dots,L_r\vdash L$ of $\pi$ (a rule instance, including zero-premise rules, or a modular axiom), the inference error polynomial
--
--   $$E=\Bigl(\prod_{j=1}^r\mathrm{App}_{L_j}\Bigr)(1-\mathrm{App}_L)$$
--
--   has a polynomial calculus derivation from the approximation errors $e_{A,j}$ and the Boolean axioms in degree at most $B\Delta$.
--
--   2. If every clause of $F$ has width at most $w$, then for each input clause line $C$ of $\pi$, the polynomial $1-\mathrm{App}_C$ is derivable from the polynomial representation $p_C$ of $C$ and its approximation errors $e_{C,j}$ in degree at most $w+\Delta$.
--
--   The lemma isolates the only place where soundness of the rules enters the size–degree relation: every failure of an approximate inference is explained, in low degree, by an approximation error.
--
--   Differences from the source:
--   - encoding: variables x_1, …, x_n → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - generalization: a fixed finite, sound and implicationally complete collection R of Frege rule schemes → any finite list R of sound de Morgan rule schemes; reason: the proof uses only soundness and finiteness of R (Lemma A.8); every source rule set is such a list
--   - generalization: input clauses and the clausal modular recursion axioms B ∨ ¬U ∨ V etc. as fixed syntactic lines → any formula that is a disjunction of exactly the clause's literals (⊥ for the empty clause), and each modular recursion clause in any order and bracketing of its three disjuncts; reason: more lines are admissible, so more proofs are covered; the source's presentation is one of them
--   - encoding: MOD_{p,a} with a ∈ 𝔽_p, residues taken modulo p → residues a : ZMod p with a - 1 computed in ZMod p; reason: same residues
--   - reading: assign consistent RS approximators (random polynomials) to all syntactic rooted subformulas → one polynomial App A per syntactic formula A satisfying Definition A.4 at every rooted subformula of every line, for some coefficients α at each randomized block; reason: the lemma is asserted for every outcome of the random choices; a single function gives identical subformulas the same approximator
--   - encoding: positive t_i indexed by depth → t : ℕ → ℕ with t i ≥ 1 for every i ≥ 1; reason: only depths of ∧/∨ blocks (≥ 1) are used; any positive t_1, …, t_ℓ extends to such t
--   - encoding: each non-input inference L_1, …, L_r ⊢ L of the proof (including zero-premise axioms) → every line L that is an instance of a rule of R whose instantiated premises occur earlier, and every line that is a modular axiom instance (error 1 − App_L); reason: every non-input inference of the proof is such an instance; the claim is made for all of them
--   - reading: a PC derivation from the e_{A,j} and the Boolean axioms in degree at most BΔ → membership in the published CD of Bool ∪ {all e_{A,j} of all rooted subformulas of π} at degree B·Δ, where 0 counts as derivable; reason: the source does not restrict which e_{A,j} may be used; the published CD includes 0, the trivial linear combination
--   - reading: 1 − App_C derivable from p_C and its approximation errors → membership in CD of Bool ∪ {p_C} ∪ {e_{C,j}} at degree w + Δ, where the e_{C,j} are the errors of the line's root block (none if the line is a literal or ⊥); reason: polynomial calculus always carries the Boolean axioms (Section 2.2); p_C is the published clause polynomial ∏(1 − ℓ_i)
--   - encoding: B = B(R, p) → ∃ B : ℕ chosen after p and R and before n, F, π, t, App and Δ; reason: the source's dependence
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Lemma A.8, printed p. 29, PDF p. 31; Equation (88), printed p. 29, PDF p. 31; Definition A.4, printed pp. 21–22, PDF pp. 23–24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_RSApproximation
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound
open ResPCDegreeSize.Main (Poly CD boolAxioms)

/-- Conneryd, STOC 2027 #332, Lemma A.8: for a prime `p` and a finite set `R` of sound Frege
rule schemes there is `B` such that, for consistent RS approximators of degree at most `Δ` on
all rooted subformulas of an AC⁰[p]-Frege proof, (i) the inference error of every rule instance
and every modular axiom line lies in `PC_{BΔ}` of the approximation errors and Boolean axioms,
and (ii) if the input CNF has width at most `w`, then `1 - App_C` of every input clause line lies
in `PC_{w+Δ}` of `p_C` and the approximation errors of that line (with the Boolean axioms). -/
theorem inference_error_derivation (p : ℕ) [Fact p.Prime] (R : List FregeRule)
    (hR : ∀ ρ ∈ R, ρ.Sound) :
    ∃ B : ℕ, ∀ (n : ℕ) (F : CNF n) (π : List (MFormula p (Fin n))), IsFregeProof R F π →
      ∀ (t : ℕ → ℕ), (∀ i, 1 ≤ i → 1 ≤ t i) →
      ∀ App : MFormula p (Fin n) → Poly n p, IsConsistentRS t App π →
      ∀ Δ : ℕ, (∀ L ∈ π, ∀ A ∈ L.subformulas, (App A).totalDegree ≤ Δ) →
        (∀ (j : ℕ) (L : MFormula p (Fin n)), π[j]? = some L →
          (∀ ρ ∈ R, ∀ σ : Fin ρ.m → MFormula p (Fin n),
              (∀ G ∈ ρ.premises, G.subst σ ∈ π.take j) → L = ρ.conclusion.subst σ →
              ruleError App ρ σ ∈ CD (boolAxioms n p ∪ proofErrors App π) (B * Δ)) ∧
          (IsModAxiom L → 1 - App L ∈ CD (boolAxioms n p ∪ proofErrors App π) (B * Δ))) ∧
        ∀ w : ℕ, (∀ C ∈ F, clauseWidth C ≤ w) →
          ∀ L ∈ π, ∀ C ∈ F, IsInputClauseFormula C L →
            1 - App L ∈
              CD (boolAxioms n p ∪ {clausePolynomial C} ∪ approxErrors App L) (w + Δ) := by sorry

end RandomCNFDeficiency.LowerBound.Supplement
