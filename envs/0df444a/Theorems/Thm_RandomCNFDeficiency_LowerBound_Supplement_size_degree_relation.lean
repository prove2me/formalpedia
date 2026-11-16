-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_Supplement_size_degree_relation
-- name    : RandomCNFDeficiency.LowerBound.Supplement.size_degree_relation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:04:40.550496+00:00
-- url     : https://prove2.me/theorems/e05291cd-423b-4b2e-bbbe-c0235b09fb8b
-- title:
--   Theorem A.3 — size–degree relation for $\mathrm{AC}^0[p]$-Frege
-- statement:
--   Fix a prime $p$ and a finite set $R$ of sound Frege rule schemes defining $\mathrm{AC}^0[p]$-Frege. There is a constant $B=B_{R,p}$ with the following property. Let $F$ be an unsatisfiable CNF on $n$ variables of width at most $w$, and let $D\ge0$ be an integer with $\operatorname{Deg}_{\mathrm{PC},\mathbb F_p}(F)>D$. Let $\ell\ge1$ and let $t_1,\dots,t_\ell$ be positive integers. Define
--
--   $$\Delta_0=1,\qquad\Delta_i=(p-1)t_i\Delta_{i-1}\quad(1\le i\le\ell).$$
--
--   Let $K$ be an integer with
--
--   $$\Delta_{\ell-1}\le K\le n,\qquad K+\max\{w+\Delta_\ell,\ B\Delta_\ell\}\le D,$$
--
--   and for $1\le i\le\ell$ let $\varepsilon_i=\rho_K(\Delta_{i-1})^{t_i}$, where $\rho_K(d)=1-(1-\tfrac1p)\frac{N_n(K-d)}{N_n(K)}$ and $N_n(j)=\sum_{u\le j}\binom nu$. Then every depth-$\ell$ $\mathrm{AC}^0[p]$-Frege refutation of $F$ satisfies
--
--   $$\sum_{i=1}^\ell M_i\varepsilon_i\ge1,$$
--
--   where $M_i$ is the number of distinct subformulas of depth $i$ whose output gate is a conjunction or disjunction, and its size $S$ satisfies
--
--   $$\ln S\ge\min_{1\le i\le\ell}\bigl(-t_i\ln\rho_K(\Delta_{i-1})\bigr).$$
--
--   Theorems A.1 and A.2 are obtained from this relation by choosing the parameters $t_i$, $K$ and $D$.
--
--   Differences from the source:
--   - encoding: variables x_1, …, x_n → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - generalization: a fixed finite, sound and implicationally complete collection R of Frege rule schemes → any finite list R of sound de Morgan rule schemes; reason: the proof uses only soundness and finiteness of R (Lemma A.8); every source rule set is such a list
--   - generalization: input clauses and the clausal modular recursion axioms B ∨ ¬U ∨ V etc. as fixed syntactic lines → any formula that is a disjunction of exactly the clause's literals (⊥ for the empty clause), and each modular recursion clause in any order and bracketing of its three disjuncts; reason: more lines are admissible, so more proofs are covered; the source's presentation is one of them
--   - reading: size = total number of symbol occurrences in the sequence → the number of occurrences of constants, variables and connectives (one per MOD gate), summed over all lines; reason: the source does not fix which symbols count; parentheses or separators only enlarge S, so a lower bound on this count implies the same bound for any such convention, and Σ M_i ≤ S still holds
--   - encoding: MOD_{p,a} with a ∈ 𝔽_p, residues taken modulo p → residues a : ZMod p with a - 1 computed in ZMod p; reason: same residues
--   - encoding: Deg_PC,𝔽_p(F) > D → every ordinary PC refutation of F over ZMod p has degree > D, compared in ℝ; reason: the minimum degree exceeds D iff every refutation's degree does
--   - reading: an unsatisfiable width-w CNF → every clause has width at most w; reason: the standard meaning; exact width w is included
--   - reading: M_i, the number of distinct subformulas of depth i with output gate ∧ or ∨ → the number of distinct rooted binary subformulas of the proof lines (including inner nodes of a block) with root ∧ or ∨ and gate-convention depth i; reason: footnote 3 and the proof of Theorem A.3 approximate every syntactic subformula and sum over all of them
--   - encoding: ln S ≥ min_{1≤i≤ℓ} −t_i ln ρ_K(Δ_{i−1}) → there is i ∈ [1, ℓ] with −t_i ln ρ_K(Δ_{i−1}) ≤ ln S; reason: a number is at least a finite minimum iff it is at least one of its terms
--   - encoding: integers D ≥ 0 and K, and t_i positive for 1 ≤ i ≤ ℓ → natural numbers D, K and t : ℕ → ℕ with t i ≥ 1 for 1 ≤ i ≤ ℓ; reason: K ≥ Δ_{ℓ−1} ≥ 1, so no integer instance is lost; t outside [1, ℓ] is unused
--   - encoding: ρ_K(d) with N_n(K − d)/N_n(K) → 1 − eta p n K d with the published eta and natural subtraction K − d; reason: Δ_{i−1} ≤ Δ_{ℓ−1} ≤ K, so no truncation occurs
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Theorem A.3, Equations (48)–(53), printed pp. 20–21, PDF pp. 22–23; Section 2.3, printed p. 8, PDF p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_RSApproximation
set_option autoImplicit false
open scoped BigOperators

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound
open ResPCDegreeSize.Main (eta)

/-- Conneryd, STOC 2027 #332, Theorem A.3 (size–degree relation): for a prime `p` and a finite
set `R` of sound Frege rule schemes there is `B` such that, for every unsatisfiable width-`w` CNF
`F` with `Deg_{PC,F_p}(F) > D`, every `ℓ ≥ 1`, positive `t_1, …, t_ℓ`, `Δ_i` as in (49), and
`K` with `Δ_{ℓ-1} ≤ K ≤ n`, `K + max(w + Δ_ℓ, BΔ_ℓ) ≤ D`, every depth-`ℓ` refutation satisfies
`∑_i M_i ε_i ≥ 1` with `ε_i = ρ_K(Δ_{i-1})^{t_i}` (52), and its size `S` satisfies
`ln S ≥ min_i -t_i ln ρ_K(Δ_{i-1})` (53). -/
theorem size_degree_relation (p : ℕ) [Fact p.Prime] (R : List FregeRule)
    (hR : ∀ ρ ∈ R, ρ.Sound) :
    ∃ B : ℕ, ∀ (n w D ℓ K : ℕ) (t : ℕ → ℕ) (F : CNF n),
      ¬ Satisfiable F → (∀ C ∈ F, clauseWidth C ≤ w) → FpDegreeExceeds p F (D : ℝ) →
      1 ≤ ℓ → (∀ i, 1 ≤ i → i ≤ ℓ → 1 ≤ t i) →
      rsDegree p t (ℓ - 1) ≤ K → K ≤ n →
      K + max (w + rsDegree p t ℓ) (B * rsDegree p t ℓ) ≤ D →
      ∀ π : List (MFormula p (Fin n)), IsFregeRefutation R F π → ProofDepthLE π ℓ →
        1 ≤ ∑ i ∈ Finset.Icc 1 ℓ,
            (gateCount π i : ℝ) * (1 - eta p n K (rsDegree p t (i - 1))) ^ t i ∧
        ∃ i ∈ Finset.Icc 1 ℓ,
          -((t i : ℝ) * Real.log (1 - eta p n K (rsDegree p t (i - 1)))) ≤
            Real.log (proofSize π : ℝ) := by sorry

end RandomCNFDeficiency.LowerBound.Supplement
