-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_modifiedSwap_pairExchange
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.modifiedSwap_pairExchange
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:14:49.448351+00:00
-- url     : https://prove2.me/theorems/7b0741e6-16bb-4069-8794-c6f3c0575369
-- title:
--   The modified SWAP exchanges adjacent Majorana pairs, with its scalar phase retained
-- statement:
--   For an existing ordered adjacent pair of wires, denote its four CAR generators by $a_0,a_1,b_0,b_1$ in wire order and define
--
--   $$S=\exp\!\left[-\frac\pi4(-a_0b_1+a_1b_0+a_0a_1+b_0b_1)\right].$$
--
--   Conjugation by $S$ exchanges the pairs: $S^\dagger a_jS=b_j$ and $S^\dagger b_jS=a_j$ for $j=0,1$. In the Jordan–Wigner representation on those wires,
--
--   $$S=-iG(Z,X)=-i(CZ)(\mathrm{SWAP}).$$
--
--   Here $G(Z,X)$ is the fermionic SWAP, rather than the ordinary SWAP alone. This operation moves Majorana pairs while respecting the quadratic construction.
--
--   **Source correction.** The sentence after Eq.(11) omits the scalar $-i$; the exchange identities are unaffected.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 12, Section 5 Eq.(11): modified SWAP implements adjacent Majorana-pair exchange

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.12: exchange of the two Majorana pairs, and corrected matrix
identification S=-i G(Z,X)=-i(CZ)(SWAP). The ordinary physical SWAP alone does
not implement this CAR exchange. The equality printed after Eq.(11) misses -i. -/
theorem modifiedSwap_pairExchange {n : ℕ} (c : CARSystem n) (w : Fin 2 ↪ Fin n)
    (hadjacent : (w 0).val + 1 = (w 1).val) :
    (∀ a b, star (modifiedSwap c.majorana w) * c.majorana (pairMajor w a b) *
        modifiedSwap c.majorana w = c.majorana (pairMajor w (Fin.rev a) b)) ∧
    modifiedSwap (jordanWigner n) w =
      (-Complex.I) • embedOp (parityGate pauliZ pauliX) w ∧
    parityGate pauliZ pauliX = (Gate.ofMatrix2 (controlled pauliZ * swapGate)).mat := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
