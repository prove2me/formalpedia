-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_noiseInternalInvariance
-- name    : QAlgorithms.Papers.Independent.Information100.P22.noiseInternalInvariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:13:25.246005+00:00
-- url     : https://prove2.me/theorems/1ce194dc-b01f-491b-9e97-1fd20348a30a
-- title:
--   §S4.2, unnumbered: noise-internal edges preserve certificate
-- statement:
--   Let $m\ge2$, $k\ge1$, fix the encoder and signal labeling, and let two simple graph cuts have the same $A_S$ and $B$, with arbitrary noise-internal adjacencies. Then
--   $$\rho_S(G)=\rho_S(H),\quad K_G=K_H,\quad C_S^G=C_S^H.$$
--   Their cut entanglement entropies agree; their exceptional-kernel tests and all-output recoverability are equivalent. This preserves the joint-signal statistics and their informational consequences. It does not assert identical authorized channels or identical decoders.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 40, §S4.2, unnumbered: noise-internal edges preserve certificate

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- PDF p.40: noise-internal changes preserve the complete signal channel and all certificates. -/
theorem noiseInternalInvariance (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q) (G H : CutGraph (Wires m k))
    (hS : G.AS = H.AS) (hB : G.B = H.B) :
    rhoS (graphVector G) = rhoS (graphVector H) ∧ cutKernel G = cutKernel H ∧
    vnEntropy (rhoS (graphVector G)) = vnEntropy (rhoS (graphVector H)) ∧
    (((cutKernel G : Set _) ⊆ exceptionalSpace P Q G.AS) ↔
      ((cutKernel H : Set _) ⊆ exceptionalSpace P Q H.AS)) ∧
    (AllRecoverable (graphVector G) (twoPauliEncoder m k P Q) ↔
      AllRecoverable (graphVector H) (twoPauliEncoder m k P Q)) ∧
    jointSignals (graphVector G) (twoPauliEncoder m k P Q) =
      jointSignals (graphVector H) (twoPauliEncoder m k P Q) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
