-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_Supplement_depth_two_tradeoff
-- name    : RandomCNFDeficiency.LowerBound.Supplement.depth_two_tradeoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:02:19.366134+00:00
-- url     : https://prove2.me/theorems/f639e15f-bc94-4a22-a025-8d7ffc4ac2fc
-- title:
--   Theorem A.2 — depth-2 tradeoff with $\exp(\Omega(\sqrt k\log n))$ size
-- statement:
--   Fix a prime $p$, a finite set $R$ of sound Frege rule schemes, and a constant $a>0$. There is a constant $c=c(p,a,R)>0$ with the following property. Let $\omega_n(1)\le k\le O(\log n)$. For all sufficiently large $n$, if $F$ is an unsatisfiable $n$-variable CNF of width at most $k$ with
--
--   $$\operatorname{Deg}_{\mathrm{PC},\mathbb F_p}(F)>\frac n2-a\frac{n}{\sqrt k},$$
--
--   then every depth-two $\mathrm{AC}^0[p]$-Frege refutation of $F$ has size
--
--   $$S\ge\exp\bigl(c\sqrt k\,\ln n\bigr).$$
--
--   Combined with Theorem 1.1 (degree above $n/2-4n/\sqrt k$ for random $k$-CNFs) this yields $\exp(\Omega_p(\log^{1.5}n))$ lower bounds for depth-two $\mathrm{AC}^0[p]$-Frege refutations of random $(\log n)$-CNFs.
--
--   Differences from the source:
--   - encoding: variables x_1, …, x_n → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - generalization: a fixed finite, sound and implicationally complete collection R of Frege rule schemes → any finite list R of sound de Morgan rule schemes; reason: the proof uses only soundness and finiteness of R (Lemma A.8); every source rule set is such a list
--   - generalization: input clauses and the clausal modular recursion axioms B ∨ ¬U ∨ V etc. as fixed syntactic lines → any formula that is a disjunction of exactly the clause's literals (⊥ for the empty clause), and each modular recursion clause in any order and bracketing of its three disjuncts; reason: more lines are admissible, so more proofs are covered; the source's presentation is one of them
--   - reading: size = total number of symbol occurrences in the sequence → the number of occurrences of constants, variables and connectives (one per MOD gate), summed over all lines; reason: the source does not fix which symbols count; parentheses or separators only enlarge S, so a lower bound on this count implies the same bound for any such convention, and Σ M_i ≤ S still holds
--   - encoding: MOD_{p,a} with a ∈ 𝔽_p, residues taken modulo p → residues a : ZMod p with a - 1 computed in ZMod p; reason: same residues
--   - encoding: Deg_PC,𝔽_p(F) > D → every ordinary PC refutation of F over ZMod p has degree > D, compared in ℝ; reason: the minimum degree exceeds D iff every refutation's degree does
--   - encoding: ω_n(1) ≤ k ≤ O(log n) → the published LogarithmicRegime k: k → ∞ and, for some C > 0, eventually 1 ≤ k ≤ n and k ≤ C log₂ n; reason: k ≤ C log₂ n already forces k ≤ n and divergence forces k ≥ 1 eventually; same regime
--   - encoding: S ≥ exp(Ω_{p,a}(√k log n)) → there is c > 0, chosen before the sequence k, the formulas and the refutations, with S ≥ exp(c √k ln n) for all large n; reason: Ω with fixed p, a (and the fixed rule set R); the base of the logarithm is absorbed into c; the threshold for n may depend on the sequence k
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Theorem A.2, Equations (45)–(46), printed p. 20, PDF p. 22; Section 2.3, printed p. 8, PDF p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_ModFrege
import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_PCDerivation
import Definitions.Def_RandomCNFDeficiency_LowerBound_RandomModel
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound

/-- Conneryd, STOC 2027 #332, Theorem A.2 (depth-2 tradeoff): fix a prime `p`, a finite set `R`
of sound Frege rule schemes and `a > 0`. There is `c > 0` such that along every sequence
`ω(1) ≤ k ≤ O(log n)`, eventually every unsatisfiable `n`-variable CNF of width at most `k` with
`Deg_{PC,F_p}(F) > n/2 - a n/√k` has only depth-two refutations of size
`≥ exp(c √k ln n)`. -/
theorem depth_two_tradeoff (p : ℕ) [Fact p.Prime] (R : List FregeRule)
    (hR : ∀ ρ ∈ R, ρ.Sound) (a : ℝ) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ → ℕ, LogarithmicRegime k →
      ∀ᶠ n : ℕ in Filter.atTop, ∀ F : CNF n, ¬ Satisfiable F →
        (∀ C ∈ F, clauseWidth C ≤ k n) →
        FpDegreeExceeds p F ((n : ℝ) / 2 - a * (n : ℝ) / Real.sqrt (k n : ℝ)) →
        ∀ π : List (MFormula p (Fin n)), IsFregeRefutation R F π → ProofDepthLE π 2 →
          Real.exp (c * Real.sqrt (k n : ℝ) * Real.log (n : ℝ)) ≤ (proofSize π : ℝ) := by sorry

end RandomCNFDeficiency.LowerBound.Supplement
