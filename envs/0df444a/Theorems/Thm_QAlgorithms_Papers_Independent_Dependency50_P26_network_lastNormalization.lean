-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_network_lastNormalization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.network_lastNormalization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:30:47.793012+00:00
-- url     : https://prove2.me/theorems/4634593b-23de-499d-b5fa-d1a5c67c90f6
-- title:
--   Lemma 4 (Normalization condition)
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $R^{(j)}$ be the actual external Choi operator of the first $j$ vertices of a deterministic, ordered CPTP memory network. With scalar prefix $R^{(0)}=1$, for each $j\ge0$ one has
--
--   $$
--   R^{(j+1)}\succeq0,\qquad\operatorname{Tr}_{H_{2j+1}}R^{(j+1)}=I_{H_{2j}}\otimes R^{(j)}.
--   $$
--
--   The earlier prefix is constructed from the same network; it is not an unrelated parameter.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 6, Lemma 4 (Normalization condition)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.6, Lemma 4: the prefix is the network actually constructed from earlier vertices. -/
theorem network_lastNormalization (s : Signature) (net : MemoryNetwork s) (n : ℕ) :
    (net.choi (n+1)).PosSemidef ∧
      traceLeft (net.choi (n+1)) =
        Matrix.kronecker (1 : Matrix (Fin (s.input n)) _ ℂ) (net.choi n) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
