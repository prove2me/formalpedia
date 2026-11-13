-- Prove2me | Theorems.Thm_PhaseEncodedQGE_lemma_A_3
-- name    : PhaseEncodedQGE.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:27.344726+00:00
-- url     : https://prove2.me/theorems/1ee57b55-f74c-4d94-8165-eccea260d26c
-- title:
--   Lemma A.3 — the Y generator $(Y_i\phi)(x)=-iz_i\phi(x\oplus e_i)$
-- statement:
--   For every vector $\phi$ of amplitudes on $n$ qubits, every qubit $i$ and every outcome $x$,
--   $$(Y_i\phi)(x)=-i\,z_i\,\phi(x\oplus e_i),$$
--   where $Y_i$ is $\sigma_Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$ acting on qubit $i$ and $z_i=(-1)^{x_i}$.
--
--   It is the step that converts the Y-mixer first-order term into flip ratios.
--
--   Differences from the source:
--   - generalization: $\phi$ the pre-mixer amplitude of App. A.1 → an arbitrary vector of amplitudes on n qubits (no graph, no preparation); reason: the proof computes the matrix entry ⟨x|Y_i|x ⊕ e_i⟩ and uses no property of φ, so the pre-mixer amplitude is a special case
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.1, p.14 (PDF p.15), Lemma A.3

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Lemma A.3, the Y generator (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. A.1.1, p.14): `(Y_i ϕ)(x) = −i z_i ϕ(x ⊕ e_i)` for every
vector `ϕ`, every qubit `i` and every outcome `x`.

**Formalization Note** `Y_i` is `site (pauli .Y) i`, the Pauli `σ_Y = [[0, −i], [i, 0]]` on qubit `i`. -/
theorem lemma_A_3 (n : ℕ) (ϕ : Outcome n → ℂ) (i : Fin n) (x : Outcome n) :
    (site (pauli .Y) i *ᵥ ϕ) x = -Complex.I * (spin x i : ℂ) * ϕ (flip x i) := by sorry

end PhaseEncodedQGE
