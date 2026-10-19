-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_constructiveCliffordDecoder
-- name    : QAlgorithms.Papers.Independent.Information100.P22.constructiveCliffordDecoder
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:58:11.836747+00:00
-- url     : https://prove2.me/theorems/c45be125-76e5-404a-a4bb-5f83b3647f27
-- title:
--   Proposition 4: Constructive Clifford decoder
-- statement:
--   Fix a certified graph realization with $m\ge2$, $k\ge1$, and $K\subseteq E$. Let $V_G$ be its encoding isometry. For every authorized subsystem $R_i=S_iN$, there are Pauli representatives $\bar X_j,\bar Z_j$ supported wholly on $R_i$, satisfying
--   $$\bar X_jV_G=V_GX_j,\qquad\bar Z_jV_G=V_GZ_j.$$
--   They have the canonical Pauli commutation/anticommutation relations. There is a Clifford $C_i$ on $R_i\simeq A'_i\otimes J_i$, with $k$ output and $mk$ junk qubits, that conjugates these representatives to $X_j\otimes I$ and $Z_j\otimes I$. Its CPTP decoder $D_i(Y)=\operatorname{Tr}_{J_i}(C_iYC_i^\dagger)$ satisfies $D_i\circ Q_i=\mathrm{id}$. This includes rank-deficient certified resources.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 10, Proposition 4: Constructive Clifford decoder

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Proposition 4, PDF p.10, proof pp.34–35. Cleaned Paulis, symplectic relations, Clifford extraction,
and the explicit CPTP partial-trace decoder. Junk has nu qubits. -/
theorem constructiveCliffordDecoder (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q) (G : CutGraph (Wires m k))
    (hcert : (cutKernel G : Set _) ⊆ exceptionalSpace P Q G.AS) :
    ∀ i : Fin m, ∃ X Z : Fin k → Op (Qubits k × Signals m k),
      ∃ C : Matrix.unitaryGroup (Qubits k × Signals m k) ℂ,
        (∀ j, AuthorizedPauli (X j) ∧ AuthorizedPauli (Z j) ∧
          liftAuthorized i (X j) * encoding (graphVector G) (twoPauliEncoder m k P Q) =
            encoding (graphVector G) (twoPauliEncoder m k P Q) * logicalAxis j .X ∧
          liftAuthorized i (Z j) * encoding (graphVector G) (twoPauliEncoder m k P Q) =
            encoding (graphVector G) (twoPauliEncoder m k P Q) * logicalAxis j .Z) ∧
        (∀ j l, X j*X l = X l*X j ∧ Z j*Z l = Z l*Z j ∧
          X j*Z l = (if j = l then (-1 : ℂ) else 1) • (Z l*X j)) ∧
        AuthorizedClifford (m := m) (k := k)
          (C : Op (Qubits k × Signals m k)) ∧
        (∀ j, (C : Op (Qubits k × Signals m k))*X j*(C : Op (Qubits k × Signals m k))ᴴ = Matrix.kronecker (logicalAxis j .X) (1 : Op (Signals m k)) ∧
          (C : Op (Qubits k × Signals m k))*Z j*(C : Op (Qubits k × Signals m k))ᴴ = Matrix.kronecker (logicalAxis j .Z) (1 : Op (Signals m k))) ∧
        IsChannel (fun Y : Op (Qubits k × Signals m k) =>
          (traceRight (conjSuperop (C : Op (Qubits k × Signals m k)) Y) : Op (Qubits k))) ∧
        ∀ Y, traceRight (conjSuperop (C : Op (Qubits k × Signals m k))
          (authorized (graphVector G) (twoPauliEncoder m k P Q) i Y)) = Y := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
