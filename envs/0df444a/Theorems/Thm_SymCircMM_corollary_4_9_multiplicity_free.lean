-- Prove2me | Theorems.Thm_SymCircMM_corollary_4_9_multiplicity_free
-- name    : SymCircMM.corollary_4_9_multiplicity_free
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:24.423203+00:00
-- url     : https://prove2.me/theorems/75fb2e27-922e-47ff-b6ed-45d8485d68a3
-- title:
--   Corollary 4.9 — multiplicity-free permutation representation $\Rightarrow C^G(\mathrm{MM}_n)=\Theta(n^3)$
-- statement:
--   Let $G\le S_n$ with $\mathrm{char}(F)\nmid|G|$, and suppose the permutation representation of $G$ over $F$ is multiplicity free. Then $C^G(\mathrm{MM}_n)=\Theta(n^3)$; explicitly:
--
--   1. every $G$-symmetric circuit $C$ computing $\mathrm{MM}_n$ has $n^3\le2\,\mathrm{size}(C)$;
--   2. some $G$-symmetric circuit computing $\mathrm{MM}_n$ has size at most $3n^3$.
--
--   The upper bound is the circuit computing each entry by one addition gate of fan-in $n$ over the products $A_{ij}B_{j\ell}$, which is $S_n$-symmetric.
--
--   **Formalization Note** Multiplicity free means that the permutation representation is the internal direct sum of a family of pairwise inequivalent irreducible subrepresentations. The lower bound covers the relaxed notion of symmetry; the circuit of item 2 is symmetric in the paper's sense (one input gate per label, every extension fixing the output gates).
--
--   Differences from the source:
--
--   - encoding: the index set [n] = {1, …, n} → a finite type ι with n = card ι; reason: a relabelling of the index set
--   - encoding: an algebraic circuit (a finite labelled multi-DAG with designated output gates) and the polynomial ĝ ∈ F[X] of each gate → Circuit F X γ on a finite gate type γ (labels, edge multiplicities wire g c, a rank function for acyclicity); gate values in MvPolynomial X F; the output gates given by a map out : ι × ι → γ; reason: the same objects; "computing MM_n" is equality of polynomials at the designated output gates
--   - generalization: a G-symmetric circuit (Definition 2.2): one input gate per variable, and σ̂ permutes (by Remark 2.4, fixes) the output gates → IsGSymmetric: for each σ ∈ G some bijection of the gates preserving edge multiplicities and labels, variables renamed by (2); input labels may repeat and nothing is required of the output gates; reason: every circuit symmetric in the paper's sense is symmetric in this sense, so the lower bound covers more circuits; the proof passes to the rigidified circuit of Proposition 4.2, where the extension is unique, and never uses the output condition
--   - encoding: a G-symmetric circuit computing MM_n (Definition 2.2 with the requirement σ̂ · g_r = g_r of Remark 2.4) → IsGSymmetricStrict G out: each label on at most one input gate, and every σ ∈ G extends to an automorphism fixing every output gate out (a, b); reason: the paper's notion for the individually invariant entries of MM_n, used for the circuit whose existence is asserted
--   - generalization: C^G(MM_n) = Θ(n³) → every G-symmetric circuit computing MM_n has n³ ≤ 2·size, and some G-symmetric circuit computing MM_n has size ≤ 3n³; reason: explicit constants, uniform in n, F and G, imply Θ(n³); both are the paper's (the naive S_n-symmetric circuit, PDF p.8, and n³/2 from Theorem 3.5, PDF p.14)
--   - encoding: char(F) ∤ |G| → (Nat.card G : F) ≠ 0; reason: a prime p divides m iff (m : F) = 0 in characteristic p, and (m : F) ≠ 0 for every m ≥ 1 in characteristic 0
--   - encoding: the permutation representation is multiplicity free (all λ_i = 1) → ∃ a family W of pairwise inequivalent irreducible subrepresentations with iSupIndep W and ⨆ W = ⊤; reason: a direct-sum decomposition into pairwise inequivalent irreducibles is exactly multiplicity one
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Corollary 4.9, p.13 (PDF p.14); naive circuit, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_SymCircMM_Circuit_IsGSymmetric
import Definitions.Def_SymCircMM_permRep

set_option autoImplicit false

namespace SymCircMM

/-- **Corollary 4.9** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.13 (PDF p.14)): "Let char(F) ∤ |G|. If the permutation representation of
G ≤ S_n over F is multiplicity free, then C^G(MM_n) = Θ(n³)."

**Formalization Note.** Multiplicity free: the permutation representation is the internal direct sum
of a family of pairwise inequivalent irreducible subrepresentations (all `λ_i = 1`). `Θ(n³)` is stated with explicit constants: every `G`-symmetric circuit computing `MM_n` has
`n³ ≤ 2 · size` (Theorem 3.5 with `N = n`: "`C^G(MM_n) ≥ n³/2`"), and some `G`-symmetric circuit
computing `MM_n` has size at most `3n³` (the circuit with one addition gate of fan-in `n` per entry over
the products `A_{ij}B_{jℓ}`, which is `S_n`-symmetric, p.7 (PDF p.8)). The lower bound covers every
circuit symmetric in the relaxed sense `IsGSymmetric` (no output condition, repeated input labels
allowed); the upper bound is a circuit symmetric in the paper's sense (`IsGSymmetricStrict`: one input
gate per label, every extension fixing the output gates). -/
theorem corollary_4_9_multiplicity_free {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Subgroup (Equiv.Perm ι)) (hG : (Nat.card G : F) ≠ 0)
    (hmf : ∃ (r : ℕ) (W : Fin r → Subrepresentation (permRep F G)),
      (∀ s, (W s).toRepresentation.IsIrreducible) ∧
      (∀ s t, s ≠ t → IsEmpty ((W s).toRepresentation.Equiv (W t).toRepresentation)) ∧
      iSupIndep (fun s => (W s).toSubmodule) ∧ (⨆ s, (W s).toSubmodule) = ⊤) :
    (∀ {γ : Type} [Fintype γ] (C : Circuit F (MMVar ι) γ), C.IsGSymmetric G → C.ComputesMM →
        Fintype.card ι ^ 3 ≤ 2 * C.size) ∧
    (∃ (γ : Type) (_ : Fintype γ) (C : Circuit F (MMVar ι) γ) (out : ι × ι → γ),
        C.IsGSymmetricStrict G out ∧ C.ComputesMMAt out ∧ C.size ≤ 3 * Fintype.card ι ^ 3) := by sorry

end SymCircMM
