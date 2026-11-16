-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_Supplement_theorem_4_1
-- name    : ReadOnceParityBP.LowerBound.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:43:40.581526+00:00
-- url     : https://prove2.me/theorems/6bfbc4f2-7d50-4005-9046-92fb4b89f27f
-- title:
--   Theorem 4.1 — Cubic arithmetic circuits and VP membership
-- statement:
--   Fix any field $F$. For each positive even integer $n$, let $f_n\in F[x_0,\ldots,x_{n-1},y_0,\ldots,y_{n-1}]$ be the complete canonical-matching polynomial of Definition 2.3. Thus $f_n$ is the sum over all sets $B\subseteq\{0,\ldots,n-1\}$ of size $n/2$ of the product of the factors $y_j(x_j+x_{\sigma_B(j)})$, where $\sigma_B$ is the paper's clockwise greedy deletion matching.
--
--   There is a positive integer $K$, independent of $n$, such that every even $n\ge2$ admits an arithmetic circuit $C_n$ over $F$, with all gates of fan-in at most two, satisfying
--
--   $$
--   C_n=f_n\quad\text{as formal polynomials},\qquad
--   \#\operatorname{wires}(C_n)\le Kn^3,\qquad
--   \#\operatorname{gates}(C_n)\le Kn^3,\qquad
--   \deg(f_n)\le n.
--   $$
--
--   Gate count includes input and constant gates; repeated uses of an input are separate wires. Together with the $2n$ variables, these size and degree bounds state membership in VP for the even-length family. This is the independent circuit upper bound accompanying the mission's lower-bound results. It applies to every field, including finite fields and characteristic zero, without fixing or specializing the $y$ variables.
--
--   **Formalization Note** The published circuit representation is a nonempty topologically ordered gate list, with sharing and the last gate as output. All references point strictly backwards. VP is nonuniform: no Turing-machine or computability hypothesis is imposed. The size constant may depend on the fixed field, and is quantified before the cycle length and circuit.
--
--   Differences from the source:
--   - encoding: cycle positions Zₙ and two n-variable blocks → Fin n and Fin n ⊕ Fin n; reason: these are the published base definitions with exactly the same canonical matching and 2n distinct variables for positive even n
--   - encoding: circuits of size O(n³), including the bounded-fan-in gate conversion on p.11 → a positive natural K before n, threshold two, fan-in at most two, and simultaneous Kn³ bounds on incoming wires and all gates; reason: the constructive proof applies at every positive even length, and binary summation and input gates change only the uniform constant
--   - encoding: f belongs to VP → the VP conditions expanded as 2n variables, degree at most n, and the cubic bounded-fan-in circuit bound; reason: each summand in Definition 2.3 has n/2 y factors and n/2 linear x factors, so the explicit degree bound and polynomial gate count retain the complete membership conclusion
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Theorem 4.1, p.10, proof pp.10–11; Definition 2.3, p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf; SHA256 7c5c47741627a753044f455a46ed6498ce421137ac1a13feef7af1183c1cf41f. PDF page equals printed page.

import Definitions.Def_ReadOnceParityBP_LowerBound_Circuit
import Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound.Supplement

/-- Ben Lee Volk, STOC 2027 submission #132 (October 2026), Theorem 4.1,
pp. 10–11, with Definition 2.3 on p. 4. Over every field, the canonical
polynomial family has cubic-size arithmetic circuits and belongs to VP.
The VP conclusion is expanded: exactly `2n` variables, degree at most `n`,
and polynomially many gates of fan-in at most two. The size constant is
chosen before the positive even cycle length; the proof permits threshold two.
`Computes` requires formal polynomial equality, including in finite fields. -/
theorem theorem_4_1 (F : Type) [Field F] :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n → Even n →
      (rsyPoly F n).totalDegree ≤ n ∧
      ∃ C : Circuit (Fin n ⊕ Fin n) F,
        C.WellFormed ∧
        C.Computes (rsyPoly F n) ∧
        (∀ g ∈ C.gates, (Circuit.Gate.children g).length ≤ 2) ∧
        C.size ≤ K * n ^ 3 ∧
        C.gates.length ≤ K * n ^ 3 := by sorry

end ReadOnceParityBP.LowerBound.Supplement
