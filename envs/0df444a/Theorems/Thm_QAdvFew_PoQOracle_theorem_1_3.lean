-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_theorem_1_3
-- name    : QAdvFew.PoQOracle.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:54:32.23865+00:00
-- url     : https://prove2.me/theorems/7957ef8d-c0bd-4bcd-98dd-64ced412ad91
-- title:
--   Theorem 1.3 — a classical oracle with $\mathsf P=\mathsf{NP}$, $\mathsf{BQP}=\mathsf{PSPACE}$, a language in $\mathsf{IP}$ hard on average, and proofs of quantumness
-- statement:
--   There is a classical oracle $O$ relative to which:
--
--   1. $\mathsf P=\mathsf{NP}$;
--   2. $\mathsf{BQP}=\mathsf{PSPACE}$;
--   3. there is a problem in $\mathsf{IP}\subseteq\mathsf{BQP}$ which is hard on average for $\mathsf P/\mathsf{poly}$: a language $L\in\mathsf{IP}^O\cap\mathsf{BQP}^O$ and a constant $\delta\in(0,1)$ such that every nonuniform PPT oracle algorithm agrees with $L$ on at most a $1-\delta$ fraction of $\{0,1\}^n$ for all sufficiently large $n$;
--   4. a polynomial-round public-coin (publicly verifiable) proof of quantumness exists;
--   5. a two-message quantumly-verifiable proof of quantumness exists.
--
--   So quantum advantage, verified classically, is consistent with the collapse of classical and quantum complexity classes that would rule out most cryptography.
--
--   Differences from the source:
--   - generalization: hard-on-average for P/poly → against every nonuniform PPT algorithm, with coins; reason: the form of Theorem 4.1(4)(a); P/poly is the case of no coins
--   - reading: hard-on-average → a constant δ ∈ (0, 1) with agreement at most 1 − δ for all sufficiently large n; reason: the paper's own statement, Theorem 4.1(4)(a)
--   - reading: a problem in IP ⊆ BQP → L ∈ IP^O and L ∈ BQP^O; reason: Remark 4.6 warns that IP^O = PSPACE^O is not claimed
--   - encoding: unbounded provers of IP → deterministic functions of the input and the transcript; reason: a randomized prover is an average of deterministic ones
--   - encoding: ≥ 1 − negl(n), ≤ negl(n) → the error and the acceptance probability are negligible functions; reason: Definition 3.26, with one fixed function per protocol
--   - encoding: classical oracles, Turing machines, the universal gate set → `Oracle = Str → Bool`, the finite-table machines `OTM`, Clifford+T with an XOR oracle gate; reason: an explicit model of the paper's §3.2 conventions; same classes
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 1.3, p. 2 (PDF p. 4)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_P
import Definitions.Def_QAdvFew_PoQOracle_NP
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_QAdvFew_PoQOracle_BQP
import Definitions.Def_QAdvFew_PoQOracle_IP
import Definitions.Def_QAdvFew_PoQOracle_NUAlg
import Definitions.Def_QAdvFew_PoQOracle_IsPoQ
import Definitions.Def_QAdvFew_PoQOracle_PublicCoin
import Definitions.Def_QAdvFew_PoQOracle_IsQvPoQ
import Definitions.Def_QAdvFew_PoQOracle_TwoMessage

namespace QAdvFew.PoQOracle

open Classical in
/-- **Theorem 1.3** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*,
arXiv:2611.05303v1, Theorem 1.3, p. 2 (PDF p. 4)). There exists a classical oracle relative to which
1. `P = NP`;
2. `BQP = PSPACE`;
3. there is a problem in `IP ⊆ BQP` which is hard-on-average for `P/poly`;
4. a polynomial-round public-coin (publicly-verifiable) proof of quantumness exists;
5. a two-message quantumly-verifiable proof of quantumness exists.

**Formalization Note** Clause 3 is the form of Theorem 4.1(4)(a): a language `L ∈ IP^O ∩ BQP^O` and
a constant `δ ∈ (0, 1)` such that every nonuniform PPT oracle algorithm (`NUAlg`, which contains
`P/poly` as the coin-free case) agrees with `L` on at most a `1 − δ` fraction of `{0,1}^n` for all
sufficiently large `n`. Clause 4 is a `CVerifier` (polynomially many rounds) with a uniform QPT
honest prover, negligible completeness and soundness errors against every nonuniform PPT classical
prover, and public coins; clause 5 a QPT verifier with one round. -/
theorem theorem_1_3 : ∃ O : Oracle,
    P O = NP O ∧
    BQP O = PSPACE O ∧
    (∃ L : Set (List Bool), L ∈ IP O ∧ L ∈ BQP O ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ A : NUAlg, ∀ᶠ n in Filter.atTop, A.success O (fun x => decide (x ∈ L)) n ≤ 1 - δ) ∧
    (∃ (V : CVerifier) (P : QParty (fun n => V.ℓ.eval n)), IsPoQ O V P ∧ PublicCoin O V) ∧
    (∃ (V : QVerifier) (P : QParty (fun n => V.ℓ.eval n)), IsQvPoQ O V P ∧ TwoMessage V) := by sorry

end QAdvFew.PoQOracle
