-- Prove2me | Theorems.Thm_QuantumPRC_lemma_3_15
-- name    : QuantumPRC.lemma_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:07.434678+00:00
-- url     : https://prove2.me/theorems/a435059d-e944-4f5e-88e4-d5a3ca5e5a26
-- title:
--   Lemma 3.15 — $U_G^\dagger Z^vX^uU_G=(-1)^{q_G(u)}X^{v\oplus Au}Z^u$
-- statement:
--   Let $G=([n],E)$ be a simple graph with adjacency matrix $A$ over $\mathbb F_2$ and let $u,v\in\mathbb F_2^n$. With the CWS encoding unitary $U_G=\big(\prod_{\{i,j\}\in E}\mathrm{CZ}_{ij}\big)H^{\otimes n}$,
--
--   $$
--   U_G^\dagger\,Z^vX^u\,U_G=(-1)^{q_G(u)}\,X^{v\oplus Au}Z^u,\qquad q_G(u):=\sum_{\{i,j\}\in E}u_iu_j .
--   $$
--
--   The lemma converts a Pauli error on a CWS codeword into a bit error $e=v\oplus Au$ and a phase error $u$, which is how the PRIC decoder separates the two (Claim 7.8).
--
--   Differences from the source: none.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Lemma 3.15, Eq. (28), p.19 (proof pp.81–82)

import Mathlib
import Definitions.Def_QuantumPRC_graphUnitary

open Matrix

namespace QuantumPRC

/-- **Lemma 3.15** (Pauli conjugation by the CWS encoding unitary). Hsieh, Yamada, arXiv:2609.38986
(sha256 6901b59d…), Lemma 3.15, p.19 (proof pp.81–82): "Let `G = ([n], E)` be a simple graph with
adjacency matrix `A` over `𝔽₂`. Let `P = Z^v X^u` with `u, v ∈ 𝔽₂^n`. Then
`U_G† P U_G = (−1)^{q_G(u)} X^{v⊕Au} Z^u`, `q_G(u) := Σ_{{i,j}∈E} u_i u_j`."

**Formalization Note.** Operators are matrices on the computational basis `Fin n → Bool`;
`Z^v X^u` and `X^{v⊕Au} Z^u` are matrix products; `U_G = (∏ CZ_{ij}) H^{⊗n}` (`graphUnitary`). -/
theorem lemma_3_15 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Bits n) :
    (graphUnitary G)ᴴ * (pauliZ v * pauliX u) * graphUnitary G =
      ((-1 : ℂ) ^ qG G u) • (pauliX (xorB v (adjMul G u)) * pauliZ u) := by sorry

end QuantumPRC
