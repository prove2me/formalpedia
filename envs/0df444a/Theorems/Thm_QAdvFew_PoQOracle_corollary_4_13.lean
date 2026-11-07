-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_corollary_4_13
-- name    : QAdvFew.PoQOracle.corollary_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:11.845705+00:00
-- url     : https://prove2.me/theorems/817f0d72-221b-4296-a729-3243226b6752
-- title:
--   Corollary 4.13 — public-coin proof of quantumness
-- statement:
--   With probability $1$ over $O\leftarrow\mathcal D$, there exists a public coin, efficiently verifiable proof of quantumness (Definition 3.26, Remark 3.27).
--
--   The verifier uses the interactive proof for salted majority to check the prover's answers on random instances, so the protocol's soundness rests on the hardness of Theorem 4.12 and its completeness on $\mathsf{PSPACE}^O\subseteq\mathsf{BQP}^O$.
--
--   Differences from the source:
--   - generalization: the oracle distribution D built from the Forrelation distribution of [RT19] → D built from any family F with the properties of Lemma 3.10 used; reason: the construction of [RT19] is one such family by Lemma 3.10, and the paper's proof uses only these properties
--   - encoding: efficiently verifiable → a classical PPT verifier with polynomially many rounds (CVerifier); reason: Definition 3.26; the polynomial round count is part of CVerifier
--   - encoding: classical oracles, Turing machines, the universal gate set → `Oracle = Str → Bool`, the finite-table machines `OTM`, Clifford+T with an XOR oracle gate; reason: an explicit model of the paper's §3.2 conventions; same classes
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Corollary 4.13, p. 30 (PDF p. 32)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_sampleABC
import Definitions.Def_QAdvFew_PoQOracle_IsPoQ
import Definitions.Def_QAdvFew_PoQOracle_PublicCoin
import Definitions.Def_QAdvFew_PoQOracle_ForrQuantum
import Definitions.Def_QAdvFew_PoQOracle_ForrAC0

open MeasureTheory

namespace QAdvFew.PoQOracle

/-- **Corollary 4.13** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Corollary 4.13, p. 30 (PDF p. 32)). With probability 1 over
`O ← D`, there exists a public coin, efficiently verifiable proof of quantumness.

**Formalization Note** `D` is built from any family `F` with properties (1) and (2) of Lemma 3.10.
"Efficiently verifiable" is a classical PPT verifier (`CVerifier`, part of `IsPoQ`), whose number of
rounds is a polynomial. -/
theorem corollary_4_13 (F : (N : ℕ) → PMF (Fin N → Bool)) (hF1 : ForrQuantum F)
    (hF2 : ForrAC0 F) :
    ∀ᵐ ω ∂(seedMeasure F), ∃ (V : CVerifier) (P : QParty (fun n => V.ℓ.eval n)),
      IsPoQ (sampleO ⊤ ω) V P ∧ PublicCoin (sampleO ⊤ ω) V := by sorry

end QAdvFew.PoQOracle
