-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_corollary_4_17
-- name    : QAdvFew.PoQOracle.corollary_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:00.272241+00:00
-- url     : https://prove2.me/theorems/1ed44782-6ed5-41c2-ac08-1649ad3caab7
-- title:
--   Corollary 4.17 — two-message quantumly-verifiable proof of quantumness
-- statement:
--   With probability $1$ over $O\leftarrow\mathcal D$, there exists a two message quantumly-verifiable proof of quantumness (Definition 3.26).
--
--   A quantum verifier can compute salted majority itself, since $h^O\in\mathsf{PSPACE}^O\subseteq\mathsf{BQP}^O$, so it needs no interactive proof.
--
--   Differences from the source:
--   - generalization: the oracle distribution D built from the Forrelation distribution of [RT19] → D built from any family F with the properties of Lemma 3.10 used; reason: the construction of [RT19] is one such family by Lemma 3.10, and the paper's proof uses only these properties
--   - encoding: classical oracles, Turing machines, the universal gate set → `Oracle = Str → Bool`, the finite-table machines `OTM`, Clifford+T with an XOR oracle gate; reason: an explicit model of the paper's §3.2 conventions; same classes
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Corollary 4.17, p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_sampleABC
import Definitions.Def_QAdvFew_PoQOracle_IsQvPoQ
import Definitions.Def_QAdvFew_PoQOracle_TwoMessage
import Definitions.Def_QAdvFew_PoQOracle_ForrQuantum
import Definitions.Def_QAdvFew_PoQOracle_ForrAC0

open MeasureTheory

namespace QAdvFew.PoQOracle

/-- **Corollary 4.17** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Corollary 4.17, p. 32 (PDF p. 34)). With probability 1 over
`O ← D`, there exists a two message quantumly-verifiable proof of quantumness.

**Formalization Note** `D` is built from any family `F` with properties (1) and (2) of Lemma 3.10.
Both the verifier and the honest prover are uniform QPT parties (`IsQvPoQ`); soundness is against
every nonuniform PPT classical prover. -/
theorem corollary_4_17 (F : (N : ℕ) → PMF (Fin N → Bool)) (hF1 : ForrQuantum F)
    (hF2 : ForrAC0 F) :
    ∀ᵐ ω ∂(seedMeasure F), ∃ (V : QVerifier) (P : QParty (fun n => V.ℓ.eval n)),
      IsQvPoQ (sampleO ⊤ ω) V P ∧ TwoMessage V := by sorry

end QAdvFew.PoQOracle
