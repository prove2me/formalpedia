-- Prove2me | Theorems.Thm_UnderstandingML_halving_mistake_bound
-- name    : UnderstandingML.halving_mistake_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:10:20.153658+00:00
-- url     : https://prove2.me/theorems/c661a877-1ab5-4b08-9eb5-374f56f27d45
-- title:
--   Theorem 21.3: for finite H, the Halving algorithm has mistake bound M_Halving(H) ≤ log₂|H|
-- statement:
--   **Theorem 21.3.** Let $H$ be a finite hypothesis class. The Halving algorithm enjoys the mistake bound $M_{\mathrm{Halving}}(H) \le \log_2(|H|)$.
--
--   Formally: $M_{\mathrm{Halving}}(H) \le \lfloor\log_2|H|\rfloor$, the number of mistakes being an integer; Halving predicts the majority label of the version space, $1$ in case of a tie.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §21.1 p. 290, Theorem 21.3

import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 21.3** (p. 290). Let `H` be a finite hypothesis class. The Halving algorithm
enjoys the mistake bound `M_Halving(H) ≤ log₂(|H|)` (the number of mistakes being an integer,
`⌊log₂ |H|⌋`). -/
theorem halving_mistake_bound {X : Type*} (H : Set (X → Bool)) (hH : H.Finite) :
    mistakeBound (halving H) H ≤ (Nat.log 2 H.ncard : ℕ∞) := by sorry

end UnderstandingML
