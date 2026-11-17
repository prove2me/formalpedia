-- Prove2me | Theorems.Thm_SqrtQueries_Supplement_theorem_1_3
-- name    : SqrtQueries.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:00:47.321657+00:00
-- url     : https://prove2.me/theorems/623fda11-22cf-45e3-a3a8-e72225786c4e
-- title:
--   Theorem 1.3 — exact square roots in $\mathsf{unitaryP}$ imply $\mathsf{BQP}=\mathsf{PSPACE}$
-- statement:
--   This is the white-box hardness result for square roots of efficient unitaries.
--
--   A **unitary language** $\mathcal U=\{U_n\}$ is a family of unitaries, $U_n$ acting on $n$ qubits. An **extension** of an $n$-qubit unitary $U$ is a unitary $\overline U$ on $n+a$ qubits with $\overline U|\psi\rangle|0^a\rangle=(U|\psi\rangle)|0^a\rangle$ for every $|\psi\rangle$. The language $\mathcal U$ belongs to $\mathsf{unitaryP}$ if there is a time-uniform family of unitary circuits $C_{n,\varepsilon}$ on $\mathrm{poly}(n,\log(1/\varepsilon))$ qubits such that for every $n$ and every $\varepsilon>0$ some extension $\overline U_n$ of $U_n$ satisfies $\|C_{n,\varepsilon}-\overline U_n\|_{\mathrm{op}}\le\varepsilon$; time-uniform means that a deterministic polynomial-time machine prints the description of $C_{n,\varepsilon}$. $\mathsf{PSPACE}$ is the class of languages decided by a deterministic Turing machine in polynomial space, and $\mathsf{BQP}$ the class of languages decided with error at most $1/3$ by uniform families of polynomial-size quantum circuits.
--
--   Consider the statement
--
--   $$
--   \text{(1)}\qquad \forall\,\mathcal U\in\mathsf{unitaryP}\ \ \exists\,\mathcal V\in\mathsf{unitaryP}\ \ \forall n\ge 1:\quad V_n^2=U_n .
--   $$
--
--   **Theorem.** Statement (1) implies
--   $$
--   \mathsf{BQP}=\mathsf{PSPACE}.
--   $$
--
--   The square roots in (1) are exact ($V_n\cdot V_n=U_n$ as matrices), while $\mathcal V$ itself only has to be approximately implementable, as membership in $\mathsf{unitaryP}$ requires. Since $\mathsf{BQP}\subseteq\mathsf{PSPACE}$ is known, the content is that efficient square roots of all efficient unitaries would let quantum polynomial time decide every polynomial-space language: quantum circuits cannot in general be efficiently "fractionalized" unless $\mathsf{BQP}=\mathsf{PSPACE}$.
--
--   **Formalization Note** The classes are the published ones of the Kretschmer–Tang development, which this paper cites for its definitions: `KTUnitary.Synth.unitaryP` and `KTUnitary.Synth.BQP` (circuits with gates whose entries have an FPTEAS encoding, time-uniform descriptions printed by one polynomial-time machine, precision $\varepsilon=2^{-l}$), both relative to the embedding of the empty language, whose oracle gates are all identities; and `QAdvFew.PoQOracle.PSPACE` with the empty oracle. Languages are sets of binary strings in both classes, and a language $A$ is in $\mathsf{BQP}$ when the promise problem $(A,A^{\mathrm c})$ is. The conclusion is an equality of these two sets of languages; hypothesis (1) is a single proposition quantifying over all of $\mathsf{unitaryP}$.
--
--   Differences from the source:
--   - encoding: unitaryP and BQP without oracle → KT26's unitaryP and BQP relative to emb ∅ (the embedding of the empty language fun _ => false); reason: emb ∅ is the identity on every number of qubits (proved in the verification file), so all its oracle gates are identities and the classes are the oracle-free ones of [KT26] that Definition 2.2 follows
--   - encoding: unitary languages {U_n}_{n≥1} → KT26's ULang, indexed by n ∈ ℕ with an extra 0-qubit member U_0; reason: (1) is equivalent with or without index 0 (extend by U_0 = V_0 = 1, which the empty circuit implements; restrict otherwise), and the square-root condition is required only for n ≥ 1 as in the source
--   - encoding: every precision ε > 0 → ε = 2^{−l} for l ∈ ℕ, the circuit family indexed by (1^n, 1^l), on n ≤ N ≤ n + p(n + l) qubits; reason: KT26 footnote 4 assumes ε = 2^{−λ} without loss of generality; poly(n, log 1/ε) qubits is n + p(n + l)
--   - encoding: Turing machines and quantum circuits of [KT26] → the published OTM machine model and UCircuit circuit structure with FPTEAS-encoded explicit gates (one encoding per family); reason: an explicit model of KT26's §4 conventions, which Definition 2.2 adopts; same classes
--   - reading: BQP, the standard class (not defined in the paper) → the language part of KT26's BQP: A ∈ BQP iff (A, Aᶜ) is decided with thresholds 2/3, 1/3 by a time-uniform family on n + poly(n) qubits measuring one designated output wire; reason: the same circuit model as unitaryP; circuits with FPTEAS-computable gate entries give the standard class
--   - encoding: PSPACE, decidable by a deterministic Turing machine in polynomial space (Definition 2.3) → QAdvFew.PoQOracle.PSPACE with the empty oracle fun _ => false (an OTM halting on every input with the right answer, within p(|x|) visited cells); reason: same class; the oracle tape is a no-op with the empty oracle
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7fe98659397cd67c1ecfceac559891ac2458052b8d31bdb7db7c5f15a), Theorem 1.3, p.4 (proved in Section 3.2, pp.20–25); definitions in Definition 2.2, p.10, and Definition 2.3, p.11

import Mathlib
import Definitions.Def_KTUnitary_Synth_ULang
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_BQP
import Definitions.Def_QAdvFew_PoQOracle_PSPACE

open QAlgorithms.Complexity

namespace SqrtQueries

namespace Supplement

/-- **Theorem 1.3 (Hardness of implementing square roots)** (Ma–Tang, *Square-root queries can
help*, STOC 2027 submission manuscript, sha256 783868e7…c5f15a, Theorem 1.3, p.4, proved in
Section 3.2, pp.20–25): consider the statement

  (1) for all `U ∈ unitaryP` there exists some `V ∈ unitaryP` such that `V_n² = U_n` for all `n ≥ 1`.

Then (1) implies `BQP = PSPACE`.

**Formalization Note (unitaryP).** `unitaryP` is "defined as in [KT26]" (p.4, Definition 2.2,
p.10): it is the published `KTUnitary.Synth.unitaryP` of Kretschmer–Tang relative to the
embedding `emb ∅` of the empty language `fun _ => false`, the series' convention for the
unrelativized class: every `O_m = emb ∅ m` is the identity, so every oracle gate, controlled or
not, of any of the four kinds is the identity and adds nothing. A unitary language `U` is a family of `n`-qubit unitaries `U n`
indexed by `n : ℕ`; the paper's languages start at `n = 1`, and the extra member `U 0` (a `1 × 1`
unitary) changes nothing: (1) with and without index `0` are equivalent, by putting `U 0 = V 0 = 1`
(implemented by the empty circuit). The precision is `ε = 2^{−l}`, `l ∈ ℕ`, and the family is
time-uniform (its descriptions are printed from `(1^n, 1^l)` by one polynomial-time machine), with
clean extensions (ancillas return to `|0^a⟩`).

**Formalization Note (square root).** `V_n² = U_n` is exact equality of `2^n × 2^n` complex
matrices, `V n * V n = U n`, for every `n ≥ 1`; `V` itself is only approximately implementable
(it lies in `unitaryP`).

**Formalization Note (BQP, PSPACE).** Both classes are sets of languages `A ⊆ {0,1}*`
(`Set Str`, `Str = List Bool`). `BQP` is the language part of the published `KTUnitary.Synth.BQP`
relative to `emb ∅`: `A ∈ BQP` iff the promise problem `(A, Aᶜ)` is decided with bounded error
`2/3`, `1/3` by a time-uniform family of polynomial-size circuits in the same circuit model as
`unitaryP`, again relative to `emb ∅`. `PSPACE` is the published `QAdvFew.PoQOracle.PSPACE` with the empty oracle
`fun _ => false` (a deterministic machine halting on every input within polynomial space;
Definition 2.3, p.11). The conclusion is the equality of the two sets of languages. -/
theorem theorem_1_3 :
    (∀ U ∈ KTUnitary.Synth.unitaryP (KTUnitary.Synth.emb (fun _ : Str => false)),
      ∃ V ∈ KTUnitary.Synth.unitaryP (KTUnitary.Synth.emb (fun _ : Str => false)), ∀ n : ℕ, 1 ≤ n →
        (V n : Matrix (Bits n) (Bits n) ℂ) * (V n : Matrix (Bits n) (Bits n) ℂ) =
          (U n : Matrix (Bits n) (Bits n) ℂ)) →
      {A : Set Str | (A, Aᶜ) ∈ KTUnitary.Synth.BQP (KTUnitary.Synth.emb (fun _ : Str => false))} =
        QAdvFew.PoQOracle.PSPACE (fun _ => false) := by sorry

end Supplement

end SqrtQueries
