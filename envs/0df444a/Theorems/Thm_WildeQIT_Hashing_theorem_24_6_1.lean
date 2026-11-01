-- Prove2me | Theorems.Thm_WildeQIT_Hashing_theorem_24_6_1
-- name    : WildeQIT.Hashing.theorem_24_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:52.959454+00:00
-- url     : https://prove2.me/theorems/4c4f71be-12fe-4a81-837b-88da3bb584cb
-- title:
--   Theorem 24.6.1: $E_1^\dagger E_2\notin N(\mathcal S)\setminus\mathcal S$ for all pairs implies $\mathcal E$ is correctable
-- statement:
--   Let $\mathcal S$ be an abelian subgroup of the $n$-qubit Pauli group $G_n=\{\pm1,\pm i\}\otimes\{I,X,Y,Z\}^{\otimes n}$, with codespace $\{|\psi\rangle : S|\psi\rangle=|\psi\rangle\ \forall S\in\mathcal S\}$, and let
--
--   $$
--   N(\mathcal S)=\{U\in\mathrm U(2^n) : U\mathcal SU^\dagger=\mathcal S\}
--   $$
--
--   be its normalizer in the unitary group. Let $\mathcal E\subseteq G_n$ be a set of errors. If every pair $E_1,E_2\in\mathcal E$ satisfies
--
--   $$
--   E_1^\dagger E_2\notin N(\mathcal S)\setminus\mathcal S ,
--   $$
--
--   then the stabilizer code corrects $\mathcal E$: there is one quantum channel $\mathcal R$ (the recovery) such that $\mathcal R(E|\psi\rangle\langle\psi|E^\dagger)=|\psi\rangle\langle\psi|$ for every error $E\in\mathcal E$ and every normalized codeword $|\psi\rangle$.
--
--   These are the error-correcting conditions for stabilizer codes; when every $E_1^\dagger E_2$ ($E_1\ne E_2$) avoids $N(\mathcal S)$ altogether the code is non-degenerate. The hashing bound applies the theorem to the set of typical Pauli errors.
--
--   **Formalization Note** $G_n$ is the published `QAlgorithms.pauliGroup n`, a subgroup of Mathlib's unitary group on `Qubits n`; $N(\mathcal S)$ is Mathlib's `Subgroup.normalizer` in that unitary group, exactly (24.97); $E_1^\dagger$ is `star E₁`. "Corrects" is the published `QAlgorithms.Corrects` on the codespace `stabilizedSpace S`: one recovery channel in Kraus form for all errors, acting on pure codewords (for a unitary error the factor $\|E\psi\|^2$ there is $1$). Pure codewords span all operators on the codespace, so the recovery also restores mixed code states and code states entangled with a reference.
--
--   Differences from the source:
--   - generalization: $E_1^\dagger E_2\notin N(\mathcal S)\setminus\mathcal S$ → $E_1^\dagger E_2\notin N(\mathcal S)\setminus\{cS : c\in\{\pm1,\pm i\},\ S\in\mathcal S\}$; reason: p. 673 works in $G_n/\{\pm1,\pm i\}$ because global phases are unobservable; the hypothesis is weaker, and the book's condition implies it since $\mathcal S$ is contained in its phase multiples
--   - reading: "it is possible to correct a set of errors $\mathcal E$" → one recovery channel restores every normalized codeword after every $E\in\mathcal E$; reason: p. 674 ("reverse these errors with the same recovery operation … $E_1|\psi\rangle=E_2|\psi\rangle$ for all states $|\psi\rangle$ in the codespace"); the book gives no formal definition
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.6.2, Theorem 24.6.1, p. 674, eq. (24.103); (24.95)–(24.97), pp. 672–673

import Definitions.Def_QAlgorithms_Defs_QECC

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 24.6.1, p. 674.
-/

namespace WildeQIT.Hashing

open QAlgorithms

/-- **Theorem 24.6.1 (error-correcting conditions for stabilizer codes)** (Wilde, *From Classical
to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 674, (24.103)). Let `S` be an abelian subgroup
of the Pauli group `Gₙ` and `E ⊆ Gₙ` a set of errors. If every pair `E₁, E₂ ∈ E` satisfies
`E₁†E₂ ∉ N(S) \ S`, then the stabilizer code of `S` corrects `E`: one recovery channel `R` maps
`E|ψ⟩⟨ψ|E†` back to `|ψ⟩⟨ψ|` for every `E ∈ E` and every normalized codeword `|ψ⟩`.

**Formalization Note.** Operators live in Mathlib's unitary group `U(2ⁿ)` on `Qubits n`;
`Gₙ` is the published `pauliGroup n`, the codespace (24.96) the published `stabilizedSpace S`,
and `N(S) = {U ∈ U(2ⁿ) : USU† = S}` (24.97) is Mathlib's `Subgroup.normalizer` taken in
`U(2ⁿ)`. "Correct" is the published `Corrects` (one channel `R` in Kraus form, the same for all
errors; for a unitary error the weight `‖Eψ‖²` is `1`). The set removed from `N(S)` is `S` up to
the phases `±1, ±i` (published `phaseMultiples S`), because the theory works in `Gₙ/{±1, ±i}`
(p. 673); this weakens the hypothesis, and the book's literal condition implies it. -/
theorem theorem_24_6_1 {n : ℕ} (S : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (hSP : S ≤ pauliGroup n) (hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (E : Set (Matrix.unitaryGroup (Qubits n) ℂ)) (hE : E ⊆ (pauliGroup n : Set _))
    (hcond : ∀ E₁ ∈ E, ∀ E₂ ∈ E,
      star E₁ * E₂ ∉ (Subgroup.normalizer (S : Set (Matrix.unitaryGroup (Qubits n) ℂ)) : Set _)
        \ phaseMultiples S) :
    Corrects (stabilizedSpace S) (Subtype.val '' E) := by sorry

end WildeQIT.Hashing
