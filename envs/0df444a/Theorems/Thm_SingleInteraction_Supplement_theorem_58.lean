-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_58
-- name    : SingleInteraction.Supplement.theorem_58
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:08:21.434274+00:00
-- url     : https://prove2.me/theorems/aa176ada-b123-4ef7-a348-fe1b08952b67
-- title:
--   Theorem 58 — universal single-interaction reduction to one fixed $(3k+3)$-local interaction with $\|H-Q^{-1}V^\dagger\tilde HV\|\le\varepsilon$
-- statement:
--   Fix $k$. There is one $(3k+3)$-qubit Hermitian interaction $h_k$ with polynomial-time computable entries, fixed independently of $H$, $n$, $Q$ and $\varepsilon$, such that for every polynomial bound $c$ there is a polynomial-time construction with the following properties. Given a $k$-local Hamiltonian $H=\sum_{i=1}^MH_i$ on $n$ qubits satisfying the assumptions of Lemma 57 ($M$, $\|H_i\|$ and the entry bit lengths at most $(n+1)^c$) and $\varepsilon>0$ with at most $(n+1)^c$ bits and $1/\varepsilon\le(n+1)^c$, it outputs a single-interaction Hamiltonian $\tilde H$ (unweighted copies of $h_k$ on pairwise distinct ordered $(3k+3)$-tuples of distinct qubits, on polynomially many qubits) and an integer $1\le Q\le\mathrm{poly}(n)$, and there is an isometry $V$ with
--   $$\Big\|H-\frac1QV^\dagger\tilde HV\Big\|\le\varepsilon.$$
--   Moreover, with output thresholds $\tilde a=Q(a+\varepsilon)$ and $\tilde b=Q(b-\varepsilon)$: if $0<\varepsilon\le(b-a)/4$, then $\lambda_{\min}(H)\le a$ implies $\lambda_{\min}(\tilde H)\le\tilde a$ and $\lambda_{\min}(H)\ge b$ implies $\lambda_{\min}(\tilde H)\ge\tilde b$.
--
--   Every constant-locality Local Hamiltonian problem therefore reduces to a single fixed unweighted interaction.
--
--   **Formalization Note** "$\mathrm{poly}(n)$" for $Q$ and the output size is $(n+1)^d$ with $d$ chosen after $c$ and before the input; the construction returns the output instance (with thresholds $\tilde a,\tilde b$) and $Q$. The isometry is a matrix $V$ with $V^\dagger V=I$.
--
--   Differences from the source:
--   - encoding: M = poly(n), ‖H_i‖ ≤ B = poly(n), entries with poly(n) bits; ε with poly(n) bits, 1/ε = O(poly(n)); Q = poly(n) → bounds (n+1)^c on the input and (n+1)^d on Q and the output size, d chosen after c; reason: the platform’s exponent convention for polynomial bounds
--   - generalization: (H, a, b) a k-Local Hamiltonian instance (so b − a ≥ 1/poly(n)) with 0 < ε ≤ (b − a)/4 → any binary-rational thresholds a, b with ε ≤ (b − a)/4; reason: the promise clause is proved for every such pair; it specializes to Local Hamiltonian instances
--   - reading: the single interaction used in H̃ → h_k Hermitian with polynomial-time computable entries; reason: Definition 31’s requirements on the common interaction
--   - encoding: the construction is promise preserving with output thresholds ã, b̃ → λmin(H) ≤ a ⇒ λmin(H̃) ≤ ã and λmin(H) ≥ b ⇒ λmin(H̃) ≥ b̃; reason: the YES/NO conditions of the Local Hamiltonian and SIH problems are these ground-energy conditions
--   - reading: integer Q = poly(n) → integer Q with 1 ≤ Q ≤ (n+1)^d; reason: Lemma 57 defines Q = max{1, ⌈M4^k/(2ε)⌉} and the proof of Theorem 58 takes that Q; Q ≥ 1 also keeps Q⁻¹ meaningful
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 58, p.52

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_sihHam
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_Supplement_Linalg
import Definitions.Def_SingleInteraction_Supplement_Variants
import Definitions.Def_SingleInteraction_Supplement_LocalHam

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding Matrix

namespace SingleInteraction

namespace Supplement

/-- Theorem 58 (Universal single-interaction reduction) (Hecker, *The Complexity of Single-Interaction
Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §4.3.3, p.52).

Fix `k`. There is one `(3k+3)`-qubit Hermitian interaction `h_k` with polynomial-time computable
entries, fixed independently of the input, and for every polynomial exponent `c` a polynomial-time
construction that maps a `k`-local Hamiltonian `H = Σ_{i=1}^M H_i` on `n` qubits satisfying the
assumptions of Lemma 57 (`M ≤ (n+1)^c`, `‖H_i‖ ≤ (n+1)^c`, entries of at most `(n+1)^c` bits) and an
`ε > 0` with at most `(n+1)^c` bits and `1/ε ≤ (n+1)^c` to a single-interaction Hamiltonian `H̃`
(unweighted copies of `h_k` on pairwise distinct ordered `(3k+3)`-tuples of distinct qubits) and an
integer `Q ≤ (n+1)^d` such that, for some isometry `V`,
$$\|H - Q^{-1} V^\dagger \tilde H V\| \le \varepsilon,$$
and the output thresholds are `ã = Q(a+ε)`, `b̃ = Q(b−ε)`; if `0 < ε ≤ (b−a)/4`, then
`λmin(H) ≤ a ⇒ λmin(H̃) ≤ ã` and `λmin(H) ≥ b ⇒ λmin(H̃) ≥ b̃`.

**Formalization Note** "`Q = poly(n)`" and the polynomial size of the output are `Q ≤ (n+1)^d` and
`ñ ≤ (n+1)^d` with `d` chosen after `c` and before the input. The construction is one function
`f`, polynomial-time on the codes, returning `(H̃, Q)` as an `SIHInstance` (with thresholds `ã, b̃`)
and a natural number. The isometry is a matrix `W` with `W†W = I`. `h_k` is asserted Hermitian with
polynomial-time computable entries, the requirement of Definition 31 on a single interaction. -/
theorem theorem_58 (k : ℕ) :
    ∃ hk : Matrix (Fin (3 * k + 3) → Fin 2) (Fin (3 * k + 3) → Fin 2) ℂ,
      hk.IsHermitian ∧ EntriesPolyTime hk ∧
      ∀ c : ℕ, ∃ (d : ℕ) (f : LHInstance × BinaryRational → SIHInstance × ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime (pair lhCodec binaryRationalCodec).encode
          (pair sihCodec natural).encode f) ∧
        ∀ (x : LHInstance) (ε : BinaryRational), LHValid k c x → EpsValid c x.n ε →
          1 ≤ (f (x, ε)).2 ∧ (f (x, ε)).2 ≤ (x.n + 1) ^ d ∧ (f (x, ε)).1.n ≤ (x.n + 1) ^ d ∧
          TuplesValid (3 * k + 3) (f (x, ε)).1.n (f (x, ε)).1.tuples ∧
          ((f (x, ε)).1.a.value : ℝ) = ((f (x, ε)).2 : ℝ) * ((x.a.value : ℝ) + (ε.value : ℝ)) ∧
          ((f (x, ε)).1.b.value : ℝ) = ((f (x, ε)).2 : ℝ) * ((x.b.value : ℝ) - (ε.value : ℝ)) ∧
          (∃ W : Matrix (Fin (f (x, ε)).1.n → Fin 2) (Fin x.n → Fin 2) ℂ, Wᴴ * W = 1 ∧
            SYKEdge.opNorm (lhHam x - (((f (x, ε)).2 : ℂ))⁻¹ •
              (Wᴴ * sihHam (3 * k + 3) hk (f (x, ε)).1 * W)) ≤ (ε.value : ℝ)) ∧
          ((ε.value : ℝ) ≤ ((x.b.value : ℝ) - (x.a.value : ℝ)) / 4 →
            (lamMin (lhHam x) ≤ (x.a.value : ℝ) →
              lamMin (sihHam (3 * k + 3) hk (f (x, ε)).1) ≤ ((f (x, ε)).1.a.value : ℝ)) ∧
            ((x.b.value : ℝ) ≤ lamMin (lhHam x) →
              ((f (x, ε)).1.b.value : ℝ) ≤ lamMin (sihHam (3 * k + 3) hk (f (x, ε)).1))) := by sorry

end Supplement

end SingleInteraction
